-- Prove2me | solution 1 for SubsetShrink.L1.f_case_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T01:19:17.656445+00:00
-- url     : https://prove2.me/submissions/b08ee153-4bef-4aa4-9bc6-ccbd7dcaf184

import Mathlib
import Definitions.Def_SubsetShrink_L1_Model
import Theorems.Thm_SubsetShrink_L1_eq_37
import Theorems.Thm_SubsetShrink_L1_sorted_bound

open SubsetShrink.L1

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (fstar ε : Fin n → ℝ) (k : ℕ) (σ δ0 lam : ℝ)
    (βhat β : Fin p → ℝ)
    (hσ : 0 < σ) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1)
    (hp : 1 ≤ p) (hF : ε ∈ SubsetShrink.Events.F X σ δ0)
    (hbest : IsL1BestSubset X (fun i => fstar i + ε i) k lam βhat)
    (hβ : SubsetShrink.Events.l0 β ≤ k)
    (hlam : (8 + 2 * Real.sqrt 2) * σ *
      Real.sqrt (Real.log (2 * (p : ℝ))) ≤ lam) :
    (SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) ≤
        (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (2 * (p : ℝ))) *
          SubsetShrink.Events.l1 (β - βhat) ∨
      SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) ≤
        (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (1 / δ0)) *
          SubsetShrink.Events.l2 (X.mulVec (β - βhat))) ∧
    (SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) ≤
        (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (2 * (p : ℝ))) *
          SubsetShrink.Events.l1 (β - βhat) →
      predictionError X fstar βhat ≤
        predictionError X fstar β + 2 * lam * SubsetShrink.Events.l1 β) := by
  have hc : 0 ≤ (4 + Real.sqrt 2) * σ := by positivity
  have hl1sym : SubsetShrink.Events.l1 (βhat - β) = SubsetShrink.Events.l1 (β - βhat) := by
    unfold SubsetShrink.Events.l1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.sub_apply]
    exact abs_sub_comm _ _
  have hl2sym : SubsetShrink.Events.l2 (X.mulVec (βhat - β)) =
      SubsetShrink.Events.l2 (X.mulVec (β - βhat)) := by
    unfold SubsetShrink.Events.l2
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    ring
  have hl1nn : ∀ v : Fin p → ℝ, 0 ≤ SubsetShrink.Events.l1 v := fun v =>
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨?_, ?_⟩
  · have h := hF (βhat - β)
    rcases le_total (SubsetShrink.Events.sortedSum (βhat - β))
        (Real.sqrt (Real.log (1 / δ0)) * SubsetShrink.Events.l2 (X.mulVec (βhat - β))) with hm | hm
    · right
      rw [max_eq_right hm, hl2sym] at h
      calc _ ≤ _ := h
        _ = _ := by ring
    · left
      rw [max_eq_left hm] at h
      have hs := sorted_bound hp (βhat - β)
      rw [hl1sym] at hs
      calc _ ≤ _ := h
        _ ≤ (4 + Real.sqrt 2) * σ *
            (Real.sqrt (Real.log (2 * (p : ℝ))) * SubsetShrink.Events.l1 (β - βhat)) :=
          mul_le_mul_of_nonneg_left hs hc
        _ = _ := by ring
  · intro ha
    have h37 := eq_37 X fstar ε k lam βhat β hbest hβ
    have htri : SubsetShrink.Events.l1 (β - βhat) ≤
        SubsetShrink.Events.l1 β + SubsetShrink.Events.l1 βhat := by
      unfold SubsetShrink.Events.l1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      simp only [Pi.sub_apply]
      exact abs_sub _ _
    have hsq : 0 ≤ Real.sqrt (Real.log (2 * (p : ℝ))) := Real.sqrt_nonneg _
    have hlam0 : 0 ≤ lam := le_trans (by positivity) hlam
    have h2 : 2 * SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) ≤
        lam * SubsetShrink.Events.l1 (β - βhat) := by
      have := mul_le_mul_of_nonneg_right hlam (hl1nn (β - βhat))
      nlinarith
    have h3 : lam * SubsetShrink.Events.l1 (β - βhat) ≤
        lam * (SubsetShrink.Events.l1 β + SubsetShrink.Events.l1 βhat) :=
      mul_le_mul_of_nonneg_left htri hlam0
    nlinarith
