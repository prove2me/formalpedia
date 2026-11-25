-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_colon_smul_top_of_flat_e37665e62fd4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:51.56147+00:00
-- url     : https://prove2.me/submissions/3122a51e-cb76-44c8-8780-64e90fdb773d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularElement
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lid_rTensor_subtype_mem_smul_top_85f2e918bd24

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing TensorProduct
open scoped Pointwise
variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution [Module.Flat A M] (J : Ideal A) (a : A) {v : M}
    (hv : a • v ∈ J • (⊤ : Submodule A M)) :
    v ∈ LinearMap.ker (J.mkQ ∘ₗ LinearMap.mulRight A a) • (⊤ : Submodule A M) := by
  set g : A →ₗ[A] A ⧸ J := J.mkQ ∘ₗ LinearMap.mulRight A a
  have hex := Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map g)
  have h0 : g.rTensor M ((1 : A) ⊗ₜ v) = 0 := by
    apply (TensorProduct.quotTensorEquivQuotSMul M J).injective
    rw [map_zero, LinearMap.rTensor_tmul]
    have : g 1 = Ideal.Quotient.mk J a := by simp [g, Ideal.Quotient.mk_eq_mk]
    rw [this, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, Submodule.Quotient.mk_eq_zero]
    exact hv
  obtain ⟨t, ht⟩ := (hex ((1 : A) ⊗ₜ v)).mp h0
  have := lid_rTensor_subtype_mem_smul_top (LinearMap.ker g) t
  rwa [ht, TensorProduct.lid_tmul, one_smul] at this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
