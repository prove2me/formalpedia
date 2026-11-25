-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_quad_upper_core_c53c0b0b1192
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:28:01.508569+00:00
-- url     : https://prove2.me/submissions/e3ac40c9-81d6-4521-abc8-57b0df14ab2b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PImTauBounds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_dot_self_nonneg_b78618d375ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_isCompact_unitSphereDot_855e9264b529
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_exists_unit_of_ne_zero_01177db69549

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
open Metric Matrix Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {Z : Type*} [TopologicalSpace Z] {g : ℕ} {K : Set Z} (hK : IsCompact K)
    (M : Z → Matrix (Fin g) (Fin g) ℝ) (hM : ContinuousOn M K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z ∈ K, ∀ v : Fin g → ℝ, v ⬝ᵥ M z *ᵥ v ≤ A * (v ⬝ᵥ v) := by
  have hΦ : Continuous fun q : Matrix (Fin g) (Fin g) ℝ × (Fin g → ℝ) => q.2 ⬝ᵥ q.1 *ᵥ q.2 :=
    continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  have hc : ContinuousOn (fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ M p.1 *ᵥ p.2)
      (K ×ˢ unitSphereDot g) :=
    hΦ.comp_continuousOn ((hM.comp continuous_fst.continuousOn fun p hp => hp.1).prodMk
      continuous_snd.continuousOn)
  obtain ⟨A, hA⟩ := (hK.prod (isCompact_unitSphereDot g)).exists_bound_of_continuousOn hc
  refine ⟨max A 0, le_max_right _ _, fun z hz v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  obtain ⟨u, hu, huM⟩ := exists_unit_of_ne_zero hv
  rw [huM]
  have h1 := hA (z, u) ⟨hz, hu⟩
  have h2 : u ⬝ᵥ M z *ᵥ u ≤ max A 0 :=
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h1)).trans (le_max_left _ _)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right h2 (dot_self_nonneg v)
end GroundTheory.Heights₂.Heights.Regular
