-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_zero_4d4e53901f14
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:24.836252+00:00
-- url     : https://prove2.me/submissions/177a5cc7-36c5-4d0f-8afc-ccf3fc71fba8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_mem_mCoordIdeal_of_aeval_eq_zero_09693c41a4b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_eval_eq_zero_of_mem_mcPts_db46e4f02c8a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    {v : ℂ} (hv : IsValueAt y 0 z v) : v = 0 := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  rw [zero_mul] at heq
  rw [eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero y hg heq), zero_div]
end GroundTheory.Heights₂.Heights.LowerBoundFree
