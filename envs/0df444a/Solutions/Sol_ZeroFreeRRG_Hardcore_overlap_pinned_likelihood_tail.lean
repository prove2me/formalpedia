-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.overlap_pinned_likelihood_tail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:02:27.202743+00:00
-- url     : https://prove2.me/submissions/41ecb53e-ff4d-4dc4-aa5b-5256bdc9acb3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_likelihood_mean_threshold
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_edge_nonnegative
import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_pinned_expectation_monotone
import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t) (η : ℝ) (hη : 0 < η) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∀ n ≥ N, Even (n*d) →
        plantedPinnedE m t s d n (fun M σ U =>
          if pinnedLL m t M σ U > (s*η^2/48)*n then 1 else 0) ≤ Real.exp (-c*n) := by
  classical
  obtain ⟨s,hs,hs1,Nmean,hmean⟩ := overlap_likelihood_mean_threshold m hm d hd t ht hC1 η hη
  let B := s*η^2/96
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨c,hc,Ntail,htail⟩ := (lemma_4_20 m hm d hd t ht).2.1 s hs.le hs1.le B hB
  have hπ : ∀ a, 0 ≤ m.pi t a := fun a => ((model_pi_positive_simplex m hm t ht).1 a).le
  have hP := model_edge_nonnegative m hm t ht
  refine ⟨s,hs,hs1,c,hc,max Nmean Ntail,?_⟩
  intro n hn heven
  have hmn := hmean n (le_trans (le_max_left _ _) hn) heven
  have htn := htail n (le_trans (le_max_right _ _) hn) heven
  have hdom : plantedPinnedE m t s d n (fun M σ U =>
      if pinnedLL m t M σ U > (s*η^2/48)*n then 1 else 0) ≤
    plantedPinnedE m t s d n (fun M σ U =>
      if pinnedLL m t M σ U - plantedPinnedE m t s d n (fun M' σ' U' => pinnedLL m t M' σ' U')
        > B*n then 1 else 0) := by
    apply planted_pinned_expectation_monotone m t s d n hπ hP hs.le hs1.le
    intro M σ U
    split_ifs with h1 h2 <;> norm_num
    dsimp [B] at *
    nlinarith
  exact hdom.trans htn
