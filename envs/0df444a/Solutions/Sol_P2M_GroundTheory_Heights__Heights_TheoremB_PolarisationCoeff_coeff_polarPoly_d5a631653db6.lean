-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_PolarisationCoeff_coeff_polarPoly_d5a631653db6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:26.74649+00:00
-- url     : https://prove2.me/submissions/d74b0b08-b85c-46c8-9587-92b927aee7e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_PPolarisationCoeff

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace PolarisationCoeff
theorem _root_.solution {σ R : Type*} [CommRing R] [Fintype σ]
    (Φ : MvPolynomial σ R →ₗ[R] R) (n : ℕ) (m : σ →₀ ℕ) :
    coeff m (polarPoly Φ n) = Φ (coeff m ((-outerDot σ R) ^ n)) := by
  classical
  unfold polarPoly
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]
end PolarisationCoeff
end GroundTheory.Heights₂.Heights.TheoremB
