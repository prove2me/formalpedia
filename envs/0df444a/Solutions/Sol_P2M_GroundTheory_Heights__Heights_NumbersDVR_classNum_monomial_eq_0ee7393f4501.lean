-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_monomial_eq_0ee7393f4501
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:35.26701+00:00
-- url     : https://prove2.me/submissions/8594c4e0-0df6-4072-a756-4a30ee7880c4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {σ : Type*} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) (c : ℤ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) :
    classNum cls (monomial μ c) Q W = c * vNumL W (classList cls μ ++ Q) := by
  classical
  rw [classNum_eq_sum cls _ Q W support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    if_pos rfl]
end GroundTheory.Heights₂.Heights.NumbersDVR
