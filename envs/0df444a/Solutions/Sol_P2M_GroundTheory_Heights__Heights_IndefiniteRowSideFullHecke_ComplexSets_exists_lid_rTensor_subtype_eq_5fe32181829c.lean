-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_lid_rTensor_subtype_eq_5fe32181829c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:31.345726+00:00
-- url     : https://prove2.me/submissions/dda20ee5-f035-4e2b-8859-99789ff6dc8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularElement

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
theorem _root_.solution (I : Ideal A) {x : M} (hx : x ∈ I • (⊤ : Submodule A M)) :
    ∃ t : I ⊗[A] M, TensorProduct.lid A M (I.subtype.rTensor M t) = x := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ⟨⟨a, ha⟩ ⊗ₜ m, by simp⟩) ?_
  rintro x x' ⟨s, rfl⟩ ⟨s', rfl⟩
  exact ⟨s + s', by rw [map_add, map_add]⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
