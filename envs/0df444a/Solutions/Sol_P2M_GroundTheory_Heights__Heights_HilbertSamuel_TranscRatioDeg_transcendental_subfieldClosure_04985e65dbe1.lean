-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_transcendental_subfieldClosure_04985e65dbe1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:06.982707+00:00
-- url     : https://prove2.me/submissions/5208fff5-2671-4882-b592-f5a46e29b750

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
theorem _root_.solution {E : Type*} [Field E] {ι : Type*} (u : ι → E) (t : E)
    (ht : Transcendental (Algebra.adjoin ℤ (Set.range u)) t) :
    Transcendental (Subfield.closure (Set.range u)) t := by
  have hR : ∀ x, x ∈ Algebra.adjoin ℤ (Set.range u) ↔ x ∈ Subring.closure (Set.range u) := fun x => by
    rw [Algebra.adjoin_int]; rfl
  set R := Algebra.adjoin ℤ (Set.range u)
  set Q := Subfield.closure (Set.range u)
  have hmem : ∀ x : R, (x : E) ∈ Q := fun x => Subfield.subring_closure_le _ ((hR x).1 x.2)
  let _ : Algebra R Q := RingHom.toAlgebra
    { toFun := fun x => ⟨x.1, hmem x⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have : IsScalarTower R Q E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FaithfulSMul R Q := (faithfulSMul_iff_algebraMap_injective R Q).2
    (fun a b h => Subtype.ext (congrArg Subtype.val h :))
  have : IsFractionRing R Q := IsFractionRing.of_field R Q (fun z => by
    obtain ⟨y, hy, z', hz', h⟩ := Subfield.mem_closure_iff.1 z.2
    exact ⟨⟨y, (hR y).2 hy⟩, ⟨z', (hR z').2 hz'⟩, Subtype.ext (by rw [Subfield.coe_div]; exact h.symm)⟩)
  intro halg
  exact ht ((IsFractionRing.isAlgebraic_iff R Q E).2 halg)
end GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
