-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_exists_div_of_mem_adjoin_ec9f4957fb2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:22.166307+00:00
-- url     : https://prove2.me/submissions/d7b85dce-5b12-4da6-ad84-0779e74e500d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFnDegRelDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
namespace GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
theorem _root_.solution {F R L : Type*} [Field F] [CommRing R] [Field L] [Algebra F L]
    (τ : R →+* L) (hF : ∀ c : F, ∃ x, τ x = algebraMap F L c) {z : L}
    (hz : z ∈ IntermediateField.adjoin F (Set.range τ)) : ∃ x y, z = τ x / τ y := by
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hz
  let S : Subalgebra F L := { τ.rangeS with algebraMap_mem' := fun c => RingHom.mem_rangeS.2 (hF c) }
  have hle : Algebra.adjoin F (Set.range τ) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨x, rfl⟩; exact RingHom.mem_rangeS.2 ⟨x, rfl⟩)
  obtain ⟨x, rfl⟩ := RingHom.mem_rangeS.1 (hle hr)
  obtain ⟨y, rfl⟩ := RingHom.mem_rangeS.1 (hle hs)
  exact ⟨x, y, rfl⟩
end GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
