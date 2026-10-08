-- Prove2me | solution 1 for WhittFLT.FirstPassage.firstPassage_continuous
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:56:05.570428+00:00
-- url     : https://prove2.me/submissions/d577c6e5-b6df-477c-955c-6c27685037ed

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage

open WhittFLT.FirstPassage Set Filter Topology
private theorem passage_ne (x : ℝ → ℝ) (hx : InE x) (t : ℝ) :
    {s : ℝ | 0 ≤ s ∧ t < x s}.Nonempty := by
  obtain ⟨y, ⟨s, hs, rfl⟩, hy⟩ := not_bddAbove_iff.mp hx.2.1 t
  exact ⟨s, hs, hy⟩
private theorem passage_bdd (x : ℝ → ℝ) (t : ℝ) :
    BddBelow {s : ℝ | 0 ≤ s ∧ t < x s} := ⟨0, fun _ h => h.1⟩
private theorem passage_nonneg (x : ℝ → ℝ) (hx : InE x) (t : ℝ) :
    0 ≤ firstPassage x t :=
  le_csInf (passage_ne x hx t) (fun _ h => h.1)
private theorem passage_upper (x : ℝ → ℝ) (hx : InE x)
    (hm : StrictMonoOn x (Ici 0)) (t b : ℝ) (hb : firstPassage x t < b) :
    t < x b := by
  obtain ⟨s, hs, hsb⟩ := exists_lt_of_csInf_lt (passage_ne x hx t) hb
  exact hs.2.trans (hm hs.1 (le_trans hs.1 (le_of_lt hsb)) hsb)
private theorem passage_lower (x : ℝ → ℝ) (hx : InE x)
    (hm : StrictMonoOn x (Ici 0)) (t a : ℝ) (ha : 0 ≤ a) (hap : a < firstPassage x t) :
    x a < t := by
  let m := (a + firstPassage x t) / 2
  have ham : a < m := by dsimp [m]; linarith
  have hmp : m < firstPassage x t := by dsimp [m]; linarith
  have hm0 : 0 ≤ m := by linarith
  have hmt : x m ≤ t := by
    by_contra hn
    have hle := csInf_le (passage_bdd x t) (show m ∈ {s | 0 ≤ s ∧ t < x s} from ⟨hm0, lt_of_not_ge hn⟩)
    change firstPassage x t ≤ m at hle
    linarith
  exact (hm ha hm0 ham).trans_le hmt

theorem solution (x : ℝ → ℝ) (hx : InE x) (hmono : StrictMonoOn x (Ici 0)) :
    ContinuousOn (firstPassage x) (Ici 0) ∧ firstPassage x 0 = 0 := by
  have hnon := passage_nonneg x hx
  constructor
  · intro t ht
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    let p := firstPassage x t
    have hup : t < x (p + ε / 2) := passage_upper x hx hmono t _ (by dsimp [p]; linarith)
    by_cases ha : 0 ≤ p - ε / 2
    · have hlo : x (p - ε / 2) < t := passage_lower x hx hmono t _ ha (by dsimp [p]; linarith)
      refine ⟨min (x (p + ε / 2) - t) (t - x (p - ε / 2)), lt_min (by linarith) (by linarith), ?_⟩
      intro u hu hdist
      rw [Real.dist_eq] at hdist ⊢
      have hd := abs_lt.mp hdist
      have huup : u < x (p + ε / 2) := by
        have := min_le_left (x (p + ε / 2) - t) (t - x (p - ε / 2))
        linarith [hd.2]
      have hulow : x (p - ε / 2) < u := by
        have := min_le_right (x (p + ε / 2) - t) (t - x (p - ε / 2))
        linarith [hd.1]
      have hpu : firstPassage x u ≤ p + ε / 2 := csInf_le (passage_bdd x u) ⟨by linarith [hnon t], huup⟩
      have hpl : p - ε / 2 ≤ firstPassage x u := by
        apply le_csInf (passage_ne x hx u)
        intro s hs
        by_contra hn
        have hsa : s < p - ε / 2 := lt_of_not_ge hn
        have := hmono hs.1 ha hsa
        linarith [hs.2]
      apply abs_lt.mpr
      change -ε < firstPassage x u - p ∧ firstPassage x u - p < ε
      constructor <;> linarith
    · refine ⟨x (p + ε / 2) - t, by linarith, ?_⟩
      intro u hu hdist
      rw [Real.dist_eq] at hdist ⊢
      have hd := abs_lt.mp hdist
      have huup : u < x (p + ε / 2) := by linarith [hd.2]
      have hpu : firstPassage x u ≤ p + ε / 2 := csInf_le (passage_bdd x u) ⟨by linarith [hnon t], huup⟩
      apply abs_lt.mpr
      change -ε < firstPassage x u - p ∧ firstPassage x u - p < ε
      have hp : p < ε / 2 := by linarith
      constructor <;> linarith [hnon u]
  · apply le_antisymm ?_ (hnon 0)
    apply le_of_forall_pos_le_add
    intro ε hε
    have hxε : 0 < x ε := lt_of_le_of_lt hx.2.2 (hmono (by simp) (le_of_lt hε) hε)
    have := csInf_le (passage_bdd x 0) (show ε ∈ {s | 0 ≤ s ∧ 0 < x s} from ⟨le_of_lt hε, hxε⟩)
    simpa [firstPassage] using this

#print axioms solution
