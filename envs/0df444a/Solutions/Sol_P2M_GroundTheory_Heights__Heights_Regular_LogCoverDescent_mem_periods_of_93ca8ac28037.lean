-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_mem_periods_of_93ca8ac28037
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:07.17054+00:00
-- url     : https://prove2.me/submissions/5d18d52c-b319-4bfa-83eb-fd35155d55ce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PLogCoverDescent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_single_mem_periods_084bea907d50

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
variable {n a : ℕ} (h : a ≤ n)
variable {h}
namespace GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
theorem _root_.solution {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) {v : Fin n → ℂ}
    (hv : ∀ k : Fin n, (k.val < a → ∃ m : ℤ, v k = m * (2 * Real.pi * Complex.I)) ∧
      (a ≤ k.val → v k = 0)) :
    v ∈ periods h φ := by
  rw [← Finset.univ_sum_single v]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  by_cases hk : k.val < a
  · obtain ⟨m, hm⟩ := (hv k).1 hk
    have e : Pi.single k (v k) = m • (Pi.single k (2 * Real.pi * Complex.I) : Fin n → ℂ) := by
      ext j
      by_cases hj : j = k
      · subst hj; simp [hm, zsmul_eq_mul]
      · simp [hj]
    rw [e]
    exact AddSubgroup.zsmul_mem _ (single_mem_periods hφ k hk) m
  · rw [(hv k).2 (by omega), Pi.single_zero]
    exact AddSubgroup.zero_mem _
end GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
