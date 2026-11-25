-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_finrank_eq_relfinrank_9ba6a3c067f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:29.444119+00:00
-- url     : https://prove2.me/submissions/6a49f7f4-e39b-49ff-9672-6e8a96e0dc22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFnDegRelDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FnDegRelDeg_isFractionRing_codRestrict_c053cfd476ba

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
theorem _root_.solution {F R₁ R₂ L : Type*} [Field F] [CommRing R₁] [CommRing R₂] [Field L]
    [Algebra F L] [Algebra R₁ R₂] (ρ : R₂ →+* L) (hρ : Function.Injective ρ)
    (E H : IntermediateField F L) (hEH : E ≤ H)
    (hτ : Function.Injective (ρ.comp (algebraMap R₁ R₂)))
    (hτE : ∀ x, ρ (algebraMap R₁ R₂ x) ∈ E) (hρH : ∀ x, ρ x ∈ H)
    (hEq : ∀ z ∈ E, ∃ x y, z = ρ (algebraMap R₁ R₂ x) / ρ (algebraMap R₁ R₂ y))
    (hHq : ∀ z ∈ H, ∃ x y, z = ρ x / ρ y) :
    Module.finrank R₁ R₂ = IntermediateField.relfinrank E H := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le hEH]
  set H' := IntermediateField.extendScalars hEH
  have hρH' : ∀ x, ρ x ∈ H' := fun x => (IntermediateField.mem_extendScalars hEH).2 (hρH x)
  let _ : Algebra R₁ E := ((ρ.comp (algebraMap R₁ R₂)).codRestrict E hτE).toAlgebra
  let _ : Algebra R₂ H' := (ρ.codRestrict H' hρH').toAlgebra
  let _ : Algebra R₁ H' := ((algebraMap R₂ H').comp (algebraMap R₁ R₂)).toAlgebra
  have : IsScalarTower R₁ R₂ H' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R₁ E H' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsFractionRing R₁ E := isFractionRing_codRestrict E _ hτ hτE hEq
  have : IsFractionRing R₂ H' := isFractionRing_codRestrict H' ρ hρ hρH' fun z hz =>
    hHq z ((IntermediateField.mem_extendScalars hEH).1 hz)
  exact (IsFractionRing.finrank_eq R₁ E R₂ H').symm
end GroundTheory.Heights₂.Heights.Targets.FnDegRelDeg
