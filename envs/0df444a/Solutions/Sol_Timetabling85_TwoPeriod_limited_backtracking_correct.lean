-- Prove2me | solution 1 for Timetabling85.TwoPeriod.limited_backtracking_correct
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:59:28.255099+00:00
-- url     : https://prove2.me/submissions/7ce249ad-d164-4d91-91d0-bb861fb98ca6

import Mathlib
import Definitions.Def_Timetabling85_TwoPeriod_Backtracking



namespace Timetabling85.TwoPeriod

open Classical

section BT
variable {n : ℕ} (G : SimpleGraph (Fin n × Bool))

lemma mem_closure_iff (S : Finset (Fin n × Bool)) (u : Fin n × Bool) :
    u ∈ closure G S ↔ InClosure G (S : Set (Fin n × Bool)) u := by
  unfold closure
  simp

lemma subset_closure (S : Finset (Fin n × Bool)) : S ⊆ closure G S := by
  intro u hu
  rw [mem_closure_iff]
  exact InClosure.base (by simpa using hu)

lemma closure_empty : closure G (∅ : Finset (Fin n × Bool)) = ∅ := by
  ext u
  rw [mem_closure_iff]
  simp only [Finset.notMem_empty, iff_false]
  intro h
  induction h with
  | base hu => simp at hu
  | force _ _ _ ih => exact ih

lemma closure_idem (S : Finset (Fin n × Bool)) : closure G (closure G S) = closure G S := by
  apply Finset.Subset.antisymm _ (subset_closure G _)
  intro u hu
  rw [mem_closure_iff] at hu ⊢
  induction hu with
  | base hu =>
    rw [Finset.mem_coe, mem_closure_iff] at hu
    exact hu
  | force _ hadj hne ih => exact InClosure.force ih hadj hne

lemma exists_of_indep_card {T : Finset (Fin n × Bool)} (hpair : ∀ j : Fin n, G.Adj (j, false) (j, true))
    (hT : G.IsNIndepSet n T) (j : Fin n) : ∃ b, (j, b) ∈ T := by
  have hinj : Set.InjOn Prod.fst (T : Set (Fin n × Bool)) := by
    intro u hu v hv huv
    by_contra hne
    have hadj : G.Adj u v := by
      obtain ⟨u1, u2⟩ := u
      obtain ⟨v1, v2⟩ := v
      simp only at huv
      subst huv
      cases u2 <;> cases v2
      · exact absurd rfl hne
      · exact hpair _
      · exact (hpair _).symm
      · exact absurd rfl hne
    exact hT.isIndepSet hu hv hne hadj
  have hcard : (T.image Prod.fst).card = n := by
    rw [Finset.card_image_of_injOn hinj]; exact hT.card_eq
  have : T.image Prod.fst = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using hcard
  have hj : j ∈ T.image Prod.fst := by rw [this]; exact Finset.mem_univ _
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
  exact ⟨u.2, hu⟩

lemma isNIndep_of_cover {T : Finset (Fin n × Bool)} (hpair : ∀ j : Fin n, G.Adj (j, false) (j, true))
    (hT : G.IsIndepSet (T : Set (Fin n × Bool))) (hc : ∀ j, ∃ b, (j, b) ∈ T) :
    G.IsNIndepSet n T := by
  refine ⟨hT, ?_⟩
  have hinj : Set.InjOn Prod.fst (T : Set (Fin n × Bool)) := by
    intro u hu v hv huv
    by_contra hne
    have hadj : G.Adj u v := by
      obtain ⟨u1, u2⟩ := u
      obtain ⟨v1, v2⟩ := v
      simp only at huv
      subst huv
      cases u2 <;> cases v2
      · exact absurd rfl hne
      · exact hpair _
      · exact (hpair _).symm
      · exact absurd rfl hne
    exact hT hu hv hne hadj
  have : T.image Prod.fst = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    obtain ⟨b, hb⟩ := hc j
    exact Finset.mem_image.mpr ⟨(j, b), hb, rfl⟩
  rw [← Finset.card_image_of_injOn hinj, this]
  simp

theorem closure_subset_core (hpair : ∀ j : Fin n, G.Adj (j, false) (j, true))
    (T : Finset (Fin n × Bool)) (hT : G.IsNIndepSet n T)
    (S : Finset (Fin n × Bool)) (hS : S ⊆ T) :
    closure G S ⊆ T := by
  intro u hu
  rw [mem_closure_iff] at hu
  induction hu with
  | base hu => exact hS (by simpa using hu)
  | @force u w hu hadj hne ih =>
    obtain ⟨b, hb⟩ := exists_of_indep_card G hpair hT w.1
    have hwT : w ∉ T := by
      intro hw
      have hwu : u ≠ w := fun h => hne (by rw [h])
      exact hT.isIndepSet ih hw hwu hadj
    cases b with
    | false =>
      have : (w.1, false) = w ∨ (w.1, false) = (w.1, !w.2) := by
        obtain ⟨w1, w2⟩ := w; cases w2 <;> simp
      rcases this with h | h
      · rw [h] at hb; exact absurd hb hwT
      · rw [h] at hb; exact hb
    | true =>
      have : (w.1, true) = w ∨ (w.1, true) = (w.1, !w.2) := by
        obtain ⟨w1, w2⟩ := w; cases w2 <;> simp
      rcases this with h | h
      · rw [h] at hb; exact absurd hb hwT
      · rw [h] at hb; exact hb

theorem autarky_core (hpair : ∀ j : Fin n, G.Adj (j, false) (j, true))
    (A : Finset (Fin n × Bool)) (hA : G.IsIndepSet (A : Set (Fin n × Bool)))
    (hclosed : closure G A = A) :
    (∃ T : Finset (Fin n × Bool), G.IsNIndepSet n T) ↔
      ∃ T : Finset (Fin n × Bool), A ⊆ T ∧ G.IsNIndepSet n T := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨A ∪ T.filter (fun u => ¬ Fixed A u.1), Finset.subset_union_left, ?_⟩
    have hind : G.IsIndepSet ((A ∪ T.filter (fun u => ¬ Fixed A u.1) : Finset _) : Set (Fin n × Bool)) := by
      intro u hu v hv hne hadj
      simp only [Finset.coe_union, Finset.coe_filter, Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe] at hu hv
      -- cross lemma
      have cross : ∀ a ∈ A, ∀ w ∈ T, ¬ Fixed A w.1 → ¬ G.Adj a w := by
        intro a ha w hw hwf hadj
        have hne1 : w.1 ≠ a.1 := by
          intro h
          apply hwf
          rw [h]
          obtain ⟨a1, a2⟩ := a
          cases a2
          · exact Or.inr ha
          · exact Or.inl ha
        have hmem : (w.1, !w.2) ∈ closure G A := by
          rw [mem_closure_iff]
          exact InClosure.force (InClosure.base (by simpa using ha)) hadj hne1
        rw [hclosed] at hmem
        apply hwf
        obtain ⟨w1, w2⟩ := w
        cases w2
        · exact Or.inl hmem
        · exact Or.inr hmem
      rcases hu with hu | ⟨hu, hu'⟩ <;> rcases hv with hv | ⟨hv, hv'⟩
      · exact hA hu hv hne hadj
      · exact cross u hu v hv hv' hadj
      · exact cross v hv u hu hu' hadj.symm
      · exact hT.isIndepSet hu hv hne hadj
    apply isNIndep_of_cover G hpair hind
    intro j
    by_cases hf : Fixed A j
    · rcases hf with h | h
      · exact ⟨true, Finset.mem_union_left _ h⟩
      · exact ⟨false, Finset.mem_union_left _ h⟩
    · obtain ⟨b, hb⟩ := exists_of_indep_card G hpair hT j
      exact ⟨b, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, hf⟩)⟩
  · rintro ⟨T, -, hT⟩
    exact ⟨T, hT⟩

theorem backtracking_core {n : ℕ} (G : SimpleGraph (Fin n × Bool))
    (hpair : ∀ j : Fin n, G.Adj (j, false) (j, true)) :
    Acc (fun t s => Step G s t) (State.run ∅) ∧
    (∀ A : Finset (Fin n × Bool), Reachable G (State.run A) → (∃ j, ¬ Fixed A j) →
      ∃ t, Step G (State.run A) t) ∧
    (∀ A : Finset (Fin n × Bool), Reachable G (State.run A) → (∀ j, Fixed A j) →
      G.IsNIndepSet n A) ∧
    (Reachable G State.fail → ¬ ∃ T : Finset (Fin n × Bool), G.IsNIndepSet n T) := by
  -- invariant
  have inv : ∀ s, Reachable G s → ∀ A, s = State.run A →
      G.IsIndepSet (A : Set (Fin n × Bool)) ∧ closure G A = A := by
    intro s hs
    induction hs with
    | refl =>
      intro A hA
      cases hA
      refine ⟨?_, closure_empty G⟩
      simp
    | tail _ hstep ih =>
      rename_i b c
      intro A hA
      cases hstep with
      | keep hnf hind =>
        cases hA
        exact ⟨hind, closure_idem G _⟩
      | reverse hnf hnind hind =>
        cases hA
        exact ⟨hind, closure_idem G _⟩
      | fail => cases hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- termination
    let μ : State n → ℕ := fun s => match s with
      | State.run A => (Finset.univ.filter (fun j => ¬ Fixed A j)).card
      | State.fail => 0
    have hdec : ∀ s t, Step G s t → μ t < μ s := by
      intro s t h
      cases h with
      | @keep A j b hnf hind =>
        show (Finset.univ.filter (fun i => ¬ Fixed (closure G (insert (j, b) A)) i)).card <
          (Finset.univ.filter (fun i => ¬ Fixed A i)).card
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨j, ?_, ?_⟩
          · simpa using hnf
          · have : (j, b) ∈ closure G (insert (j, b) A) := subset_closure G _ (Finset.mem_insert_self _ _)
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
            cases b
            · exact Or.inr this
            · exact Or.inl this
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          intro hf
          apply hi
          rcases hf with h | h
          · exact Or.inl (subset_closure G _ (Finset.mem_insert_of_mem h))
          · exact Or.inr (subset_closure G _ (Finset.mem_insert_of_mem h))
      | @reverse A j b hnf hnind hind =>
        show (Finset.univ.filter (fun i => ¬ Fixed (closure G (insert (j, !b) A)) i)).card <
          (Finset.univ.filter (fun i => ¬ Fixed A i)).card
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨j, ?_, ?_⟩
          · simpa using hnf
          · have : (j, !b) ∈ closure G (insert (j, !b) A) := subset_closure G _ (Finset.mem_insert_self _ _)
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
            cases b
            · exact Or.inl this
            · exact Or.inr this
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          intro hf
          apply hi
          rcases hf with h | h
          · exact Or.inl (subset_closure G _ (Finset.mem_insert_of_mem h))
          · exact Or.inr (subset_closure G _ (Finset.mem_insert_of_mem h))
      | @fail A j b hnf _ _ =>
        show 0 < (Finset.univ.filter (fun i => ¬ Fixed A i)).card
        exact Finset.card_pos.mpr ⟨j, by simpa using hnf⟩
    have hwf : WellFounded (fun t s => Step G s t) := by
      apply Subrelation.wf (r := fun t s => μ t < μ s)
      · intro t s h; exact hdec s t h
      · exact (InvImage.wf μ wellFounded_lt)
    exact hwf.apply _
  · -- progress
    intro A _ ⟨j, hj⟩
    by_cases h1 : G.IsIndepSet (closure G (insert (j, true) A) : Set (Fin n × Bool))
    · exact ⟨_, Step.keep hj h1⟩
    · by_cases h2 : G.IsIndepSet (closure G (insert (j, !true) A) : Set (Fin n × Bool))
      · exact ⟨_, Step.reverse hj h1 h2⟩
      · exact ⟨_, Step.fail hj h1 h2⟩
  · -- success
    intro A hr hall
    obtain ⟨hind, -⟩ := inv _ hr A rfl
    apply isNIndep_of_cover G hpair hind
    intro j
    rcases hall j with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  · -- failure
    intro hr
    rcases Relation.ReflTransGen.cases_tail hr with h | ⟨b, hb, hstep⟩
    · cases h
    · cases hstep with
      | @fail A j c hnf h1 h2 =>
        have hreach : Reachable G (State.run A) := hb
        obtain ⟨hind, hcl⟩ := inv _ hreach A rfl
        rintro ⟨T, hT⟩
        obtain ⟨T', hAT', hT'⟩ := (autarky_core G hpair A hind hcl).mp ⟨T, hT⟩
        obtain ⟨d, hd⟩ := exists_of_indep_card G hpair hT' j
        have hd' : d = c ∨ d = !c := by cases c <;> cases d <;> simp
        have key : ∀ e, (j, e) ∈ T' → G.IsIndepSet (closure G (insert (j, e) A) : Set (Fin n × Bool)) := by
          intro e he
          have hsub : closure G (insert (j, e) A) ⊆ T' :=
            closure_subset_core G hpair T' hT' _ (Finset.insert_subset he hAT')
          exact hT'.isIndepSet.mono (by exact_mod_cast hsub)
        rcases hd' with rfl | rfl
        · exact h1 (key _ hd)
        · exact h2 (key _ hd)

end BT
end Timetabling85.TwoPeriod

open Timetabling85.TwoPeriod


theorem solution {n : ℕ} (G : SimpleGraph (Fin n × Bool))
    (hpair : ∀ j : Fin n, G.Adj (j, false) (j, true)) :
    Acc (fun t s => Step G s t) (State.run ∅) ∧
    (∀ A : Finset (Fin n × Bool), Reachable G (State.run A) → (∃ j, ¬ Fixed A j) →
      ∃ t, Step G (State.run A) t) ∧
    (∀ A : Finset (Fin n × Bool), Reachable G (State.run A) → (∀ j, Fixed A j) →
      G.IsNIndepSet n A) ∧
    (Reachable G State.fail → ¬ ∃ T : Finset (Fin n × Bool), G.IsNIndepSet n T) := by
  exact backtracking_core G hpair
