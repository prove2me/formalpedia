-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_isFractionRing_codRestrict_c053cfd476ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:23.732932+00:00
-- url     : https://prove2.me/submissions/1b30ac94-c3f8-4a65-a789-1365393f724f

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
theorem _root_.solution {R L F' : Type*} [CommRing R] [Field L] [Field F'] [Algebra F' L]
    (E : IntermediateField F' L) (τ : R →+* L) (hτ : Function.Injective τ) (hmem : ∀ x, τ x ∈ E)
    (hq : ∀ z ∈ E, ∃ x y, z = τ x / τ y) :
    letI := (τ.codRestrict E hmem).toAlgebra
    IsFractionRing R E := by
  let _ := (τ.codRestrict E hmem).toAlgebra
  have hinj : Function.Injective (algebraMap R E) := fun a b h => hτ (congrArg Subtype.val h)
  have : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).2 hinj
  refine IsFractionRing.of_field R E fun z => ?_
  obtain ⟨x, y, hxy⟩ := hq z z.2
  refine ⟨x, y, Subtype.ext ?_⟩
  rw [IntermediateField.coe_div]
  exact hxy
end GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
