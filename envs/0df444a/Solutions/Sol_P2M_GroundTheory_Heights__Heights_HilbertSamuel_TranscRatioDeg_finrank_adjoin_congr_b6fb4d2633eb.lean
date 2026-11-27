-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_finrank_adjoin_congr_b6fb4d2633eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:57:44.750771+00:00
-- url     : https://prove2.me/submissions/99737801-7324-4fb1-ae71-959e5fc1c31f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LinearIndependentAdjoinOfTranscendental

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
open Polynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
theorem _root_.solution {E Φ L : Type*} [Field E] [Field Φ] [Field L] [Algebra Φ E] [Algebra L E]
    {S T : Set E} (h : (algebraMap Φ E).fieldRange = (algebraMap L E).fieldRange)
    (hST : Subfield.closure (Set.range (algebraMap Φ E) ∪ S) =
      Subfield.closure (Set.range (algebraMap L E) ∪ T)) :
    Module.finrank Φ (IntermediateField.adjoin Φ S) = Module.finrank L (IntermediateField.adjoin L T) := by
  let i : Φ ≃+* L := ((algebraMap Φ E).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr h)).trans
    (algebraMap L E).rangeRestrictFieldEquiv.symm
  have hi : ∀ r, algebraMap L E (i r) = algebraMap Φ E r := fun r => by
    simp only [i, RingEquiv.trans_apply, RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
    rfl
  have hmem : ∀ x : E, x ∈ IntermediateField.adjoin Φ S ↔ x ∈ IntermediateField.adjoin L T := fun x => by
    rw [← IntermediateField.mem_toSubfield, ← IntermediateField.mem_toSubfield,
      IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield, hST]
  let j : IntermediateField.adjoin Φ S ≃+ IntermediateField.adjoin L T :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩, invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }
  have hr := rank_eq_of_equiv_equiv i j i.bijective (fun r m => Subtype.ext (by
    simp only [j, AddEquiv.coe_mk, Equiv.coe_fn_mk, Algebra.smul_def]
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul]
    exact congrArg (· * (m : E)) (hi r).symm))
  exact congrArg Cardinal.toNat hr
end GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
