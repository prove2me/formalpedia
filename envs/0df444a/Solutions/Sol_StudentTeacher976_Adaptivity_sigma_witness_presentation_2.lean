-- Prove2me | solution 2 for StudentTeacher976.Adaptivity.sigma_witness_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:54:37.756734+00:00
-- url     : https://prove2.me/submissions/f9fc2b66-86e4-4470-8703-d77f02c471f3

import Definitions.Def_StudentTeacher976_Adaptivity_Auxiliary
import Theorems.Thm_StudentTeacher976_Adaptivity_delta_regular_restrict
import Theorems.Thm_StudentTeacher976_Adaptivity_oracle_false_mem_delta
import Theorems.Thm_StudentTeacher976_Adaptivity_residual_quantifier_padding


set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity

private def haltMachine (b : Bool) : OTM where
  k := 0
  g := 0
  δ := fun _ a c => (if b then 1 else 2, a, 1, c, 1)

private theorem haltMachine_result (b : Bool) (O : Oracle) (x : Word) :
    (haltMachine b).result O x 1 = some b := by
  cases b <;> rfl

private theorem altLen_const (lengths : List ℕ) (start : Bool) (P : Prop) :
    AvgPHETH.AltLen lengths start (fun _ => P) ↔ P := by
  induction lengths generalizing start with
  | nil => rfl
  | cons n ns ih =>
    cases start with
    | false =>
      simp only [AvgPHETH.AltLen, ih]
      constructor
      · intro h; exact h (List.replicate n false) (by simp)
      · exact fun h _ _ => h
    | true =>
      simp only [AvgPHETH.AltLen, ih]
      constructor
      · rintro ⟨w, hw, h⟩; exact h
      · intro h; exact ⟨List.replicate n false, by simp, h⟩

 theorem empty_mem_sigma (i : ℕ) : (∅ : Language) ∈ Sigma i := by
  refine ⟨haltMachine false, 1, List.replicate i 0, by simp, ?_, ?_⟩
  · intro s
    simpa using congrArg Option.isSome (haltMachine_result false (fun _ => false) s)
  · intro x
    simp only [Set.mem_empty_iff_false]
    have hres : ∀ ys : List Word,
        (haltMachine false).result (fun _ => false) (tup (x :: ys))
          ((1 : Polynomial ℕ).eval (tup (x :: ys)).length) = some true ↔ False := by
      intro ys
      simp [haltMachine_result]
    simp only [hres]
    exact (altLen_const _ true False).symm

 theorem univ_mem_sigma (i : ℕ) : (Set.univ : Language) ∈ Sigma i := by
  refine ⟨haltMachine true, 1, List.replicate i 0, by simp, ?_, ?_⟩
  · intro s
    simpa using congrArg Option.isSome (haltMachine_result true (fun _ => false) s)
  · intro x
    simp only [Set.mem_univ]
    have hres : ∀ ys : List Word,
        (haltMachine true).result (fun _ => false) (tup (x :: ys))
          ((1 : Polynomial ℕ).eval (tup (x :: ys)).length) = some true ↔ True := by
      intro ys
      simp [haltMachine_result]
    simp only [hres]
    exact (altLen_const _ true True).symm


end StudentTeacher976.Adaptivity

set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity

private def pairNext (q : Fin 8) (b : Bool) : Fin 8 :=
  match q.val with
  | 0 => if b then 1 else 2
  | 1 => 0
  | 2 => if b then 7 else 3
  | 3 => if b then 4 else 5
  | 4 => 3
  | 5 => if b then 7 else 6
  | _ => 7

 def pairDFA : OTM.Precheck.DFA where
  size := 8
  start := 0
  next := pairNext
  accept := fun q => decide (q = 6)

private def component (u : Word) : Word := u.flatMap (fun b => [true, b]) ++ [false, false]

private theorem dead_run (s : Word) : s.foldl pairNext 7 = 7 := by
  induction s with
  | nil => rfl
  | cons b s ih => simpa [pairNext] using ih

private theorem terminal_run (s : Word) : s.foldl pairNext 6 = 6 ↔ s = [] := by
  cases s with
  | nil => simp
  | cons b s => simp [pairNext, dead_run]

private theorem component_run (u rest : Word) (boundary : Bool) :
    (component u ++ rest).foldl pairNext (if boundary then 3 else 0) =
      rest.foldl pairNext (if boundary then 6 else 3) := by
  induction u with
  | nil => cases boundary <;> rfl
  | cons b u ih =>
    cases boundary <;> simpa [component, pairNext, List.append_assoc] using ih

private theorem first_component (s : Word) (boundary : Bool)
    (h : s.foldl pairNext (if boundary then 3 else 0) = 6) :
    ∃ u rest, s = component u ++ rest ∧ rest.foldl pairNext (if boundary then 6 else 3) = 6 := by
  induction s using List.twoStepInduction generalizing boundary with
  | nil => cases boundary <;> norm_num [Fin.ext_iff] at h
  | singleton b => cases boundary <;> cases b <;> norm_num [pairNext, Fin.ext_iff] at h
  | cons_cons b c rest ih ih1 =>
    cases b with
    | false =>
      cases c with
      | false =>
        refine ⟨[], rest, rfl, ?_⟩
        cases boundary <;> simpa [pairNext] using h
      | true =>
        cases boundary <;> simp [pairNext, dead_run] at h
    | true =>
      have hr : rest.foldl pairNext (if boundary then 3 else 0) = 6 := by
        cases boundary <;> simpa [pairNext] using h
      obtain ⟨u, suffix, hu, hrun⟩ := ih boundary hr
      refine ⟨c :: u, suffix, ?_, hrun⟩
      simp [component, hu, List.append_assoc]

 theorem pairDFA_spec (s : Word) : pairDFA.accept (pairDFA.run s) = true ↔ ∃ u v, s = tup [u, v] := by
  change decide (s.foldl pairNext 0 = 6) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨u, rest, hs, hr⟩ := first_component s false h
    obtain ⟨v, suffix, hv, hvend⟩ := first_component rest true hr
    have hend : suffix = [] := terminal_run suffix |>.mp hvend
    refine ⟨u, v, ?_⟩
    simp [hs, hv, hend, component, tup, List.append_assoc]
  · rintro ⟨u, v, rfl⟩
    have heq : tup [u, v] = component u ++ component v := by simp [tup, component, List.append_assoc]
    rw [heq]
    have h := component_run u (component v) false
    change (component u ++ component v).foldl pairNext 0 = 6
    simp only [Bool.false_eq_true, if_false] at h
    rw [h]
    have h' := component_run v [] true
    simpa using h'

private theorem read_component (u rest : Word) : readComponent (component u ++ rest) = some (u, rest) := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [component, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    simpa [readComponent] using congrArg (fun o => o.map (fun p : Word × Word => (b :: p.1, p.2))) ih

 theorem tup_pair_injective {x y u v : Word} (h : tup [x, y] = tup [u, v]) : x = u ∧ y = v := by
  have hcode : ∀ a b : Word, tup [a, b] = component a ++ tup [b] := by
    intro a b
    simp [tup, component, List.append_assoc]
  have hfirst := congrArg readComponent h
  rw [hcode, hcode, read_component, read_component] at hfirst
  have hpair : x = u ∧ tup [y] = tup [v] := by simpa using hfirst
  have hsingle : ∀ a : Word, tup [a] = component a ++ [] := by intro a; simp [tup, component]
  have hsecond := congrArg readComponent hpair.2
  rw [hsingle, hsingle, read_component, read_component] at hsecond
  exact ⟨hpair.1, congrArg Prod.fst (Option.some.inj hsecond)⟩

end StudentTeacher976.Adaptivity

set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity

 theorem sigma_one_witness (L : Language) (hL : L ∈ Sigma 1) :
    Nonempty (WitnessPresentation 0 L) := by
  obtain ⟨V, clock, ps, hps, htotal, hdec⟩ := hL
  cases ps with
  | nil => simp at hps
  | cons p ps =>
    have hnil : ps = [] := by simpa using hps
    subst ps
    let Lang : Language := {s | V.result (fun _ => false) s (clock.eval s.length) = some true}
    have hLang : Lang ∈ Delta 0 := by
      refine ⟨fun _ => false, V, clock, ?_, htotal, ?_⟩
      · simpa using empty_mem_sigma 0
      · intro x; rfl
    have hreg := delta_regular_restrict hLang pairDFA
    refine ⟨{ length := p
              test := fun x y => V.result (fun _ => false) (tup [x, y])
                (clock.eval (tup [x, y]).length) = some true
              efficient := ?_
              represents := ?_ }⟩
    · have hset : {s | ∃ x y, s = tup [x, y] ∧
          V.result (fun _ => false) (tup [x, y]) (clock.eval (tup [x, y]).length) = some true} =
          Lang ∩ {x | pairDFA.accept (pairDFA.run x) = true} := by
        ext s
        change (∃ x y, s = tup [x, y] ∧ _) ↔
          (V.result (fun _ => false) s (clock.eval s.length) = some true ∧ _)
        simp only [Set.mem_setOf_eq]
        rw [pairDFA_spec]
        constructor
        · rintro ⟨x, y, rfl, hxy⟩
          exact ⟨hxy, x, y, rfl⟩
        · rintro ⟨hV, x, y, hxy⟩
          refine ⟨x, y, hxy, ?_⟩
          rwa [← hxy]
      rw [hset]
      exact hreg
    · intro x
      simpa [AvgPHETH.AltLen] using hdec x

end StudentTeacher976.Adaptivity

set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity

 theorem witness_from_residual (i : ℕ) (L : Language) (p : Polynomial ℕ)
    (ps : List (Polynomial ℕ)) (V : OTM) (clock : Polynomial ℕ)
    (hLrep : ∀ x : Word, x ∈ L ↔ ∃ y : Word, y.length = p.eval x.length ∧
      AvgPHETH.AltLen (ps.map fun b => b.eval x.length) false
        (fun ys => V.result (fun _ => false) (tup (x :: y :: ys))
          (clock.eval (tup (x :: y :: ys)).length) = some true))
    (hres : {s | ∃ x y : Word, s = tup [x, y] ∧
      ¬ AvgPHETH.AltLen (ps.map fun b => b.eval x.length) false
        (fun ys => V.result (fun _ => false) (tup (x :: y :: ys))
          (clock.eval (tup (x :: y :: ys)).length) = some true)} ∈ Sigma i) :
    Nonempty (WitnessPresentation i L) := by
  classical
  let A : Language := {s | ∃ x y : Word, s = tup [x, y] ∧
      ¬ AvgPHETH.AltLen (ps.map fun b => b.eval x.length) false
        (fun ys => V.result (fun _ => false) (tup (x :: y :: ys))
          (clock.eval (tup (x :: y :: ys)).length) = some true)}
  let O : Oracle := fun s => decide (s ∈ A)
  have hOeq : {s | O s = true} = A := by ext s; simp [O]
  have hO : {s | O s = true} ∈ Sigma i := by rw [hOeq]; exact hres
  have hpair : ∀ x y : Word, O (tup [x, y]) = true ↔
      ¬ AvgPHETH.AltLen (ps.map fun b => b.eval x.length) false
        (fun ys => V.result (fun _ => false) (tup (x :: y :: ys))
          (clock.eval (tup (x :: y :: ys)).length) = some true) := by
    intro x y
    change decide (∃ a b : Word, tup [x, y] = tup [a, b] ∧ _) = true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hab, hn⟩
      obtain ⟨ha, hb⟩ := tup_pair_injective hab
      simpa [← ha, ← hb] using hn
    · intro hn; exact ⟨x, y, rfl, hn⟩
  have hfalse : ∀ x y : Word, O (tup [x, y]) = false ↔
      AvgPHETH.AltLen (ps.map fun b => b.eval x.length) false
        (fun ys => V.result (fun _ => false) (tup (x :: y :: ys))
          (clock.eval (tup (x :: y :: ys)).length) = some true) := by
    intro x y
    have hbool : O (tup [x, y]) = false ↔ ¬ O (tup [x, y]) = true := by cases O (tup [x, y]) <;> simp
    rw [hbool, hpair, not_not]
  have hreg := delta_regular_restrict (oracle_false_mem_delta i O hO) pairDFA
  refine ⟨{ length := p
            test := fun x y => O (tup [x, y]) = false
            efficient := ?_
            represents := ?_ }⟩
  · have hset : {s | ∃ x y : Word, s = tup [x, y] ∧ O (tup [x, y]) = false} =
        {s | O s = false} ∩ {s | pairDFA.accept (pairDFA.run s) = true} := by
      ext s
      change (∃ x y : Word, s = tup [x, y] ∧ _) ↔ (O s = false ∧ _)
      simp only [Set.mem_setOf_eq]
      rw [pairDFA_spec]
      constructor
      · rintro ⟨x, y, rfl, hxy⟩; exact ⟨hxy, x, y, rfl⟩
      · rintro ⟨hs, x, y, hxy⟩
        exact ⟨x, y, hxy, by rwa [← hxy]⟩
    rw [hset]
    exact hreg
  · intro x
    rw [hLrep x]
    apply exists_congr
    intro y
    exact and_congr_right fun _ => (hfalse x y).symm

end StudentTeacher976.Adaptivity

set_option autoImplicit false
open StudentTeacher976.Adaptivity

theorem solution (i : ℕ) (L : Language)
    (hL : L ∈ StudentTeacher976.Adaptivity.Sigma (i + 1)) :
    Nonempty (WitnessPresentation i L) := by
  cases i with
  | zero => exact sigma_one_witness L hL
  | succ i =>
    obtain ⟨V, clock, ps, hps, htotal, hdec⟩ := hL
    cases ps with
    | nil => simp at hps
    | cons p ps =>
      apply witness_from_residual (i + 1) L p ps V clock
      · intro x
        simpa [AvgPHETH.AltLen] using hdec x
      · exact residual_quantifier_padding (i + 1) (by omega) V clock ps (by simpa using hps) htotal
