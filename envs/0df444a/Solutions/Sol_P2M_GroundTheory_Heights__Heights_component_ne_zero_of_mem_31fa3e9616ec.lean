-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_component_ne_zero_of_mem_31fa3e9616ec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:53.513256+00:00
-- url     : https://prove2.me/submissions/bdb39bff-fdf3-4b97-86be-0e03c0e9d277

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_weightSet_ae282eab400e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {R σ : Type*} [CommRing R] {w : σ → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {p : MvPolynomial σ R} {a : ℕ} (ha : a ∈ weightSet w p) :
    weightedHomogeneousComponent w a p ≠ 0 := by
  classical
  obtain ⟨d, hd, rfl⟩ := mem_weightSet.mp ha
  intro h
  have := congrArg (coeff d) h
  rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
  exact mem_support_iff.mp hd this
end GroundTheory.Heights₂.Heights
