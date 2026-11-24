-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_comp_addMonoidHom_c2a78c747026
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:24.567848+00:00
-- url     : https://prove2.me/submissions/1aa7bf42-1307-46aa-b84d-f69183416ef6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_5b25825b175f

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
theorem _root_.solution (φ : M →+ M') (hφ : Function.Injective φ)
    (w : σ → M) (b : M) (f : MvPolynomial σ R) :
    weightedHomogeneousComponent (fun v => φ (w v)) (φ b) f = weightedHomogeneousComponent w b f := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent,
    weight_comp_addMonoidHom, hφ.eq_iff]
end GroundTheory.Heights₂.Heights.NumbersDVR
