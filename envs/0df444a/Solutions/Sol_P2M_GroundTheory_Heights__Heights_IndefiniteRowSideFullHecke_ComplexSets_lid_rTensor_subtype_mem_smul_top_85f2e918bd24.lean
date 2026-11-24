-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lid_rTensor_subtype_mem_smul_top_85f2e918bd24
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:40.575136+00:00
-- url     : https://prove2.me/submissions/1de24706-f2d2-4c4a-9d54-2e1a4925e25d

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
theorem _root_.solution (I : Ideal A) (t : I ⊗[A] M) :
    TensorProduct.lid A M (I.subtype.rTensor M t) ∈ I • (⊤ : Submodule A M) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul i m => simpa using Submodule.smul_mem_smul i.2 Submodule.mem_top
  | add s t hs ht => rw [map_add, map_add]; exact add_mem hs ht
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
