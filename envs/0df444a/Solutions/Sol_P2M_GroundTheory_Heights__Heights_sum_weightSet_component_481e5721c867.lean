-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sum_weightSet_component_481e5721c867
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:51.29231+00:00
-- url     : https://prove2.me/submissions/ff1a445b-585e-4c11-8436-eb3e8018530f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree

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
theorem _root_.solution (p : MvPolynomial σ R) :
    ∑ a ∈ weightSet w p, weightedHomogeneousComponent w a p = p := by
  classical
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    exact Finset.mem_image.mpr ⟨d, mem_support_iff.mpr (Ne.symm hne), rfl⟩
end GroundTheory.Heights₂.Heights
