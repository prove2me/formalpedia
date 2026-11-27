-- Prove2me | solution 1 for PigeonholeSearch.exists_polynomial_shared_clause_search
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T02:40:57.744938+00:00
-- url     : https://prove2.me/submissions/af9ad2cb-9633-4d49-afb4-92119fbdd759

import Definitions.Def_PigeonholeSearch

open PigeonholeSearch

private abbrev LiteralTest (n : ℕ) := Fin (n+1) × Fin n × Bool

private def tests {n : ℕ} : Clause n → List (LiteralTest n)
  | .row p => (List.finRange n).map fun h => (p,h,false)
  | .collision p q h _ => [(p,h,true),(q,h,true)]

private def testBit {n : ℕ} (x : Assignment n) (v : LiteralTest n) : Bool :=
  x v.1 v.2.1 == v.2.2

private theorem test_correct {n : ℕ} (x : Assignment n) (c : Clause n) :
    (tests c).all (testBit x) = true ↔ c.violated x := by
  cases c <;> simp [tests, testBit, Clause.violated, List.all_eq_true]

private def build {n : ℕ} (hit miss : Tree n) : List (LiteralTest n) → Tree n
  | [] => hit
  | (p,h,false) :: vs => .query p h (build hit miss vs) miss
  | (p,h,true) :: vs => .query p h miss (build hit miss vs)

private theorem run_build {n : ℕ} (x : Assignment n) (hit miss : Tree n)
    (vs : List (LiteralTest n)) :
    (build hit miss vs).run x = if vs.all (testBit x) then hit.run x else miss.run x := by
  induction vs with
  | nil => simp [build]
  | cons v vs ih =>
    obtain ⟨p,h,b⟩ := v
    cases b <;> cases hv : x p h <;> simp [build, Tree.run, testBit, hv, ih]

private def Closed {n : ℕ} (S : Finset (Tree n)) : Prop :=
  ∀ p h no yes, Tree.query p h no yes ∈ S → no ∈ S ∧ yes ∈ S

private theorem build_states {n : ℕ} (hit miss : Tree n) (S : Finset (Tree n))
    (closed : Closed S) (hh : hit ∈ S) (hm : miss ∈ S) (vs : List (LiteralTest n)) :
    ∃ U : Finset (Tree n), Closed U ∧ build hit miss vs ∈ U ∧ S ⊆ U ∧
      U.card ≤ S.card + vs.length := by
  classical
  induction vs with
  | nil => exact ⟨S,closed,hh,Finset.Subset.refl _,by simp⟩
  | cons v vs ih =>
    obtain ⟨U, cu, tail, sub, bound⟩ := ih
    obtain ⟨p,h,b⟩ := v
    let root := build hit miss ((p,h,b)::vs)
    refine ⟨insert root U,?_,Finset.mem_insert_self ..,sub.trans (Finset.subset_insert ..),?_⟩
    · intro p' h' no yes node
      rcases Finset.mem_insert.mp node with eq | old
      · have missU := sub hm
        cases b <;> simp [root, build] at eq <;> obtain ⟨rfl,rfl,rfl,rfl⟩ := eq <;>
          simp_all
      · exact ⟨Finset.mem_insert_of_mem (cu _ _ _ _ old).1,
          Finset.mem_insert_of_mem (cu _ _ _ _ old).2⟩
    · have := Finset.card_insert_le root U
      simp only [List.length_cons]; omega

private def search {n : ℕ} (fallback : Tree n) : List (Clause n) → Tree n
  | [] => fallback
  | c :: cs => build (.leaf c) (search fallback cs) (tests c)

private theorem search_correct {n : ℕ} (x : Assignment n) (fallback : Tree n)
    (cs : List (Clause n)) (existsBad : ∃ c ∈ cs, c.violated x) :
    ((search fallback cs).run x).violated x := by
  induction cs with
  | nil => simp at existsBad
  | cons c cs ih =>
    rw [search,run_build]
    by_cases bad : c.violated x
    · simpa [(test_correct x c).mpr bad,Tree.run] using bad
    · have no : (tests c).all (testBit x) = false := by
        cases h : (tests c).all (testBit x) with
        | false => rfl
        | true => exact False.elim (bad ((test_correct x c).mp h))
      simp [no]
      apply ih
      obtain ⟨q, mem, hq⟩ := existsBad
      exact ⟨q,(List.mem_cons.mp mem).resolve_left (fun eq => bad (eq ▸ hq)),hq⟩

private theorem search_states {n : ℕ} (fallback : Clause n) (cs : List (Clause n)) :
    ∃ U : Finset (Tree n), Closed U ∧ search (.leaf fallback) cs ∈ U ∧
      U.card ≤ 1 + (n+3)*cs.length := by
  classical
  induction cs with
  | nil => exact ⟨{.leaf fallback},by simp [Closed],by simp [search],by simp⟩
  | cons c cs ih =>
    obtain ⟨S, closed, mem, bound⟩ := ih
    let V := insert (Tree.leaf c) S
    have cv : Closed V := by
      intro p h no yes a
      have old : Tree.query p h no yes ∈ S := by simpa [V] using a
      exact ⟨Finset.mem_insert_of_mem (closed _ _ _ _ old).1,
        Finset.mem_insert_of_mem (closed _ _ _ _ old).2⟩
    obtain ⟨U,cu,top,_,size⟩ := build_states (.leaf c) _ V cv (Finset.mem_insert_self ..)
      (Finset.mem_insert_of_mem mem) (tests c)
    refine ⟨U,cu,top,?_⟩
    have add : V.card ≤ S.card+1 := Finset.card_insert_le .. 
    have len : (tests c).length ≤ n+2 := by cases c <;> simp [tests]
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]; omega

private theorem some_violation {n : ℕ} (x : Assignment n) : ∃ c : Clause n, c.violated x := by
  classical
  by_cases empty : ∃ p, ∀ h, x p h = false
  · obtain ⟨p,hp⟩ := empty
    exact ⟨.row p,hp⟩
  have occupied (p : Fin (n+1)) : ∃ h, x p h = true := by
    by_contra! none
    exact empty ⟨p, fun h => by specialize none h; cases hv : x p h <;> simp_all⟩
  choose f hf using occupied
  obtain ⟨p,q,ne,same⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  exact ⟨.collision p q (f p) ne, hf p, same ▸ hf q⟩

private def labelCode {n : ℕ} : Clause n → Fin (n+1) ⊕ (Fin (n+1) × Fin (n+1) × Fin n)
  | .row p => .inl p
  | .collision p q h _ => .inr (p,q,h)

private theorem code_injective {n : ℕ} : Function.Injective (labelCode (n:=n)) := by
  intro a b eq
  cases a <;> cases b <;> simp_all [labelCode]

theorem solution (n : ℕ) :
    ∃ (t : Tree n) (states : Finset (Tree n)), t ∈ states ∧
      (∀ p h no yes, Tree.query p h no yes ∈ states → no ∈ states ∧ yes ∈ states) ∧
      (∀ x : Assignment n, (t.run x).violated x) ∧
      states.card ≤ 1 + (n+3)*((n+1) + (n+1)*((n+1)*n)) := by
  classical
  let _ : Fintype (Clause n) := Fintype.ofInjective labelCode code_injective
  let cs := (Finset.univ : Finset (Clause n)).toList
  obtain ⟨states,closed,mem,size⟩ := search_states (.row 0) cs
  refine ⟨_,states,mem,closed,?_,?_⟩
  · intro x
    obtain ⟨c, bad⟩ := some_violation x
    exact search_correct x _ cs ⟨c,by simp [cs],bad⟩
  · have card := Fintype.card_le_of_injective (labelCode (n:=n)) code_injective
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at card
    exact size.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by simpa [cs] using card)) _)
