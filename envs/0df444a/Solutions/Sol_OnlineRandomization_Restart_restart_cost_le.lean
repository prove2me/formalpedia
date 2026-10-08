-- Prove2me | solution 1 for OnlineRandomization.Restart.restart_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:13:25.83643+00:00
-- url     : https://prove2.me/submissions/fcbf12ca-0cb3-4e1c-8699-1eb2528c43c9

import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model
import Definitions.Def_OnlineRandomization_Restart_GameProperties
import Definitions.Def_OnlineRandomization_Restart_RestartAlgorithm



namespace OnlineRandomization.Restart

lemma orx_opt_le_cost {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (r : List R)
    (a : List A) (hl : a.length = r.length) : F.opt r ≤ F.cost r a := by
  unfold Game.opt
  have hof : List.ofFn (fun i : Fin r.length => a.get (Fin.cast hl.symm i)) = a := by
    apply List.ext_get <;> simp [hl]
  calc _ ≤ F.cost r (List.ofFn (fun i : Fin r.length => a.get (Fin.cast hl.symm i))) :=
        Finset.inf'_le (fun f : Fin r.length → A => F.cost r (List.ofFn f))
          (Finset.mem_univ (fun i : Fin r.length => a.get (Fin.cast hl.symm i)))
    _ = _ := by rw [hof]

lemma orx_le_opt {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (r : List R) (x : ℝ)
    (h : ∀ a : List A, a.length = r.length → x ≤ F.cost r a) : x ≤ F.opt r :=
  Finset.le_inf' _ _ (fun f _ => h _ (by simp))

lemma orx_opt_snoc {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (hmono : IsMonotone F)
    (r : List R) (t : R) : F.opt r ≤ F.opt (r ++ [t]) := by
  apply orx_le_opt
  intro a ha
  have hne : a ≠ [] := by intro h; subst h; simp at ha
  rw [← List.dropLast_append_getLast hne]
  have hl : a.dropLast.length = r.length := by simp at ha; simp [ha]
  exact (orx_opt_le_cost F r _ hl).trans (hmono r a.dropLast t _ hl.symm)

lemma orx_opt_prefix {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (hmono : IsMonotone F)
    (p q : List R) (h : p <+: q) : F.opt p ≤ F.opt q := by
  obtain ⟨l, rfl⟩ := h
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    rw [← List.append_assoc]; exact ih.trans (orx_opt_snoc F hmono _ x)

lemma orx_opt_nil {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) :
    F.opt ([] : List R) = F.cost [] [] := by
  apply le_antisymm (orx_opt_le_cost F [] [] rfl)
  apply orx_le_opt; intro a ha; simp at ha; subst ha; rfl

lemma orx_answers_snoc {R A : Type*} (G : DetAlg R A) (r : List R) (x : R) :
    G.answers (r ++ [x]) = G.answers r ++ [G (r ++ [x])] := by
  simp only [DetAlg.answers, List.length_append, List.length_singleton, List.range_succ,
    List.map_append, List.map_singleton]
  congr 1
  · apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_of_length_le (by simp)]

lemma orx_answers_length {R A : Type*} (G : DetAlg R A) (r : List R) :
    (G.answers r).length = r.length := by simp [DetAlg.answers]

lemma orx_InRH_nil {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ) :
    InRH F H ([] : List R) := by
  intro r' h hne; exact absurd (List.prefix_nil.mp h) hne

lemma orx_InRH_single {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (hf0 : F.cost [] [] ≤ H) (x : R) : InRH F H [x] := by
  intro r' h hne
  obtain ⟨t, ht⟩ := h
  rcases List.append_eq_singleton_iff.mp ht with ⟨h1, _⟩ | ⟨h1, _⟩
  · subst h1; rw [orx_opt_nil]; exact hf0
  · exact absurd h1 hne

lemma orx_state_snoc {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (r : List R) (x : R) :
    restartState F H (r ++ [x]) = restartStep F H (restartState F H r) x := by
  simp [restartState, List.foldl_append]

lemma orx_inv {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (hf0 : F.cost [] [] ≤ H) (AH : DetAlg R A) (r : List R) :
    r = (restartState F H r).1.flatten ++ (restartState F H r).2 ∧
    (restart F H AH).answers r =
      ((restartState F H r).1.map AH.answers).flatten ++ AH.answers (restartState F H r).2 ∧
    (∀ s ∈ (restartState F H r).1, InRH F H s) ∧ InRH F H (restartState F H r).2 ∧
    ((restartState F H r).2 = [] → r = []) := by
  induction r using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [restartState], by simp [restartState, DetAlg.answers], by simp [restartState],
      by simp [restartState]; exact orx_InRH_nil F H, fun _ => rfl⟩
  | append_singleton r x ih =>
    rw [orx_answers_snoc]
    have hcs : restart F H AH (r ++ [x]) = AH (restartStep F H (restartState F H r) x).2 := by
      simp [restart, currentSegment, orx_state_snoc]
    rw [hcs, orx_state_snoc]
    generalize restartState F H r = st at ih ⊢
    obtain ⟨C, c⟩ := st
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    simp only at h1 h2 h3 h4 h5
    by_cases hc : c = []
    · subst hc
      have hstep : restartStep F H (C, []) x = (C, [x]) := by simp [restartStep]
      rw [hstep]
      refine ⟨by simp [h1], ?_, h3, orx_InRH_single F H hf0 x, by simp⟩
      rw [h2]; simp [DetAlg.answers]
    · by_cases hin : InRH F H (c ++ [x])
      · have hstep : restartStep F H (C, c) x = (C, c ++ [x]) := by simp [restartStep, hin]
        rw [hstep]
        refine ⟨by rw [h1]; simp, ?_, h3, hin, by simp⟩
        rw [h2, orx_answers_snoc]; simp
      · have hstep : restartStep F H (C, c) x = (C ++ [c], [x]) := by simp [restartStep, hin, hc]
        rw [hstep]
        refine ⟨by rw [h1]; simp, ?_, ?_, orx_InRH_single F H hf0 x, by simp⟩
        · rw [h2]; simp [DetAlg.answers]
        · intro s hs; simp at hs; rcases hs with hs | hs
          · exact h3 s hs
          · subst hs; exact h4


theorem rh_finite_core {R A : Type*} [Finite R] [Fintype A] [Nonempty A] (F : Game R A)
    (hloc : IsLocal F) (H : ℝ) :
    {r : List R | InRH F H r}.Finite := by
  have hS : {r : List R | F.opt r ≤ max H 1}.Finite := hloc _ (by positivity)
  have hfin : ({[]} ∪ (fun p : List R × R => p.1 ++ [p.2]) ''
      ({r : List R | F.opt r ≤ max H 1} ×ˢ Set.univ)).Finite :=
    (Set.finite_singleton _).union ((hS.prod Set.finite_univ).image _)
  apply hfin.subset
  intro r hr
  rcases List.eq_nil_or_concat r with h | ⟨L, b, h⟩
  · left; exact h
  · right
    rw [List.concat_eq_append] at h
    refine ⟨(L, b), ⟨?_, trivial⟩, h.symm⟩
    have := hr L (by rw [h]; exact List.prefix_append _ _) (by rw [h]; simp)
    exact le_trans this (le_max_left _ _)

lemma orx_closed_ge {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A)
    (hmono : IsMonotone F) (H : ℝ) (r : List R) :
    ∀ s ∈ (restartState F H r).1, H ≤ F.opt s := by
  induction r using List.reverseRecOn with
  | nil => simp [restartState]
  | append_singleton r x ih =>
    rw [orx_state_snoc]
    generalize restartState F H r = st at ih ⊢
    obtain ⟨C, c⟩ := st
    simp only at ih
    unfold restartStep
    split_ifs with h
    · intro s hs; simp at hs; rcases hs with hs | hs
      · exact ih s hs
      · rw [hs]
        obtain ⟨_, h2⟩ := h
        simp only [InRH, not_forall] at h2
        obtain ⟨r', hp, hne, hlt⟩ := h2
        have hp' : r' <+: c := by
          rcases List.prefix_concat_iff.mp hp with h | h
          · exact absurd h hne
          · exact h
        exact (le_of_lt (not_le.mp hlt)).trans (orx_opt_prefix F hmono _ _ hp')
    · exact ih

theorem segment_opt_ge_core {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A)
    (hmono : IsMonotone F) (H : ℝ) (r : List R) :
    ∀ s ∈ (segments F H r).dropLast, H ≤ F.opt s := by
  intro s hs
  apply orx_closed_ge F hmono H r
  unfold segments at hs
  split_ifs at hs
  · exact List.mem_of_mem_dropLast hs
  · rwa [List.dropLast_concat] at hs

theorem opt_ge_sum_segments_core {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (D : ℝ)
    (hD : DiameterBound F D) (segs : List (List R)) (hsegs : segs ≠ []) :
    (segs.map F.opt).sum - ((segs.length : ℝ) - 1) * D ≤ F.opt segs.flatten := by
  induction segs with
  | nil => exact absurd rfl hsegs
  | cons s rest ih =>
    by_cases hr : rest = []
    · subst hr; simp
    · have ih := ih hr
      simp only [List.map_cons, List.sum_cons, List.length_cons, List.flatten_cons]
      have key : F.opt s + F.opt rest.flatten - D ≤ F.opt (s ++ rest.flatten) := by
        apply orx_le_opt
        intro a ha
        rw [List.length_append] at ha
        have h1 : (a.take s.length).length = s.length := by rw [List.length_take]; omega
        have h2 : (a.drop s.length).length = rest.flatten.length := by
          rw [List.length_drop]; omega
        have hd := hD s (a.take s.length) rest.flatten (a.drop s.length) h1.symm h2.symm
        unfold discrepancy at hd
        rw [List.take_append_drop] at hd
        have := (abs_le.mp hd).1
        have := orx_opt_le_cost F s _ h1
        have := orx_opt_le_cost F rest.flatten _ h2
        linarith
      push_cast
      linarith

lemma orx_cost_flatten_le {R A : Type*} (F : Game R A) (D : ℝ) (hD : DiameterBound F D)
    (g : List R → List A) (hg : ∀ s, (g s).length = s.length) (segs : List (List R))
    (hne : segs ≠ []) :
    F.cost segs.flatten (segs.map g).flatten ≤
      (segs.map fun s => F.cost s (g s)).sum + ((segs.length : ℝ) - 1) * D := by
  induction segs with
  | nil => exact absurd rfl hne
  | cons s rest ih =>
    by_cases hr : rest = []
    · subst hr; simp
    · have ih := ih hr
      simp only [List.map_cons, List.sum_cons, List.length_cons, List.flatten_cons]
      have hl : ((rest.map g).flatten).length = rest.flatten.length := by
        simp [List.length_flatten, Function.comp_def, hg]
      have hd := hD s (g s) rest.flatten (rest.map g).flatten (hg s).symm hl.symm
      unfold discrepancy at hd
      have := (abs_le.mp hd).2
      push_cast
      linarith

lemma orx_sum_le {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (H : ℝ)
    (α : ℝ → ℝ) (AH : DetAlg R A)
    (hAH : ∀ r : List R, InRH F H r → AH.costOn F r ≤ α (F.opt r)) (l : List (List R))
    (hl : ∀ s ∈ l, InRH F H s) :
    (l.map fun s => F.cost s (AH.answers s)).sum ≤ (l.map fun s => α (F.opt s)).sum := by
  induction l with
  | nil => simp
  | cons s rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have := hAH s (hl s (by simp))
    have := ih (fun t ht => hl t (by simp [ht]))
    unfold DetAlg.costOn at *
    linarith

theorem restart_cost_le_core {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (D H : ℝ)
    (hD : DiameterBound F D) (hf0 : F.cost [] [] ≤ H) (α : ℝ → ℝ) (AH : DetAlg R A)
    (hAH : ∀ r : List R, InRH F H r → AH.costOn F r ≤ α (F.opt r))
    (r : List R) (hr : r ≠ []) :
    (restart F H AH).costOn F r ≤
      ((segments F H r).map (fun s => α (F.opt s))).sum
        + (((segments F H r).length : ℝ) - 1) * D := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := orx_inv F H hf0 AH r
  have hc : (restartState F H r).2 ≠ [] := fun h => hr (h5 h)
  have hseg : segments F H r = (restartState F H r).1 ++ [(restartState F H r).2] := by
    simp [segments, hc]
  rw [hseg]
  unfold DetAlg.costOn
  have hr' : r = ((restartState F H r).1 ++ [(restartState F H r).2]).flatten := by
    simpa using h1
  have ha : (restart F H AH).answers r =
      (((restartState F H r).1 ++ [(restartState F H r).2]).map AH.answers).flatten := by
    simpa using h2
  rw [ha]
  have key := orx_cost_flatten_le F D hD AH.answers (orx_answers_length AH)
    ((restartState F H r).1 ++ [(restartState F H r).2]) (by simp)
  rw [← hr'] at key
  have := orx_sum_le F H α AH hAH ((restartState F H r).1 ++ [(restartState F H r).2])
    (by intro s hs; simp at hs; rcases hs with hs | hs
        · exact h3 s hs
        · subst hs; exact h4)
  linarith

end OnlineRandomization.Restart

open OnlineRandomization.Restart


theorem solution {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (D H : ℝ)
    (hD : DiameterBound F D) (hf0 : F.cost [] [] ≤ H) (α : ℝ → ℝ) (AH : DetAlg R A)
    (hAH : ∀ r : List R, InRH F H r → AH.costOn F r ≤ α (F.opt r))
    (r : List R) (hr : r ≠ []) :
    (restart F H AH).costOn F r ≤
      ((segments F H r).map (fun s => α (F.opt s))).sum
        + (((segments F H r).length : ℝ) - 1) * D := by
  exact restart_cost_le_core F D H hD hf0 α AH hAH r hr
