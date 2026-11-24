-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_5b25825b175f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:03.676801+00:00
-- url     : https://prove2.me/submissions/5aca754d-02e6-44f6-8516-35c3a2971fa9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog

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
variable {σ R M M' : Type*} [CommRing R] [AddCommMonoid M] [AddCommMonoid M']
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (φ : M →+ M') (w : σ → M) (d : σ →₀ ℕ) :
    Finsupp.weight (fun v => φ (w v)) d = φ (Finsupp.weight w d) := by
  simp [Finsupp.weight_apply, map_finsuppSum, map_nsmul]
end GroundTheory.Heights₂.Heights.NumbersDVR
