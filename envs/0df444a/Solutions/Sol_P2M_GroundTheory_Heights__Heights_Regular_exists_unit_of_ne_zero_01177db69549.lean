-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_exists_unit_of_ne_zero_01177db69549
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:59.220572+00:00
-- url     : https://prove2.me/submissions/9fa81f2a-41f8-450a-9b1a-99bf25f5ff95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PImTauBounds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_quad_smul_092261aee0d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_dot_self_nonneg_b78618d375ca

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
theorem _root_.solution {g : ℕ} {v : Fin g → ℝ} (hv : v ≠ 0) :
    ∃ u ∈ unitSphereDot g, ∀ M : Matrix (Fin g) (Fin g) ℝ,
      v ⬝ᵥ M *ᵥ v = (v ⬝ᵥ v) * (u ⬝ᵥ M *ᵥ u) := by
  have hpos : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (dot_self_nonneg v) (fun h => hv (dotProduct_self_eq_zero.mp h.symm))
  set s := Real.sqrt (v ⬝ᵥ v) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hs2 : s ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
  have hvu : v = s • (s⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  refine ⟨s⁻¹ • v, ?_, fun M => ?_⟩
  · show (s⁻¹ • v) ⬝ᵥ (s⁻¹ • v) = 1
    have := quad_smul (1 : Matrix (Fin g) (Fin g) ℝ) s⁻¹ v
    rw [one_mulVec, one_mulVec] at this
    rw [this, ← hs2]; field_simp
  · conv_lhs => rw [hvu]
    rw [quad_smul, hs2]
end GroundTheory.Heights₂.Heights.Regular
