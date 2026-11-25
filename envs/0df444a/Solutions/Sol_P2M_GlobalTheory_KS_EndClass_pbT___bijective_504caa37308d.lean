-- Prove2me | solution 1 for P2M_GlobalTheory_KS_EndClass_pbT___bijective_504caa37308d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:39.802309+00:00
-- url     : https://prove2.me/submissions/b80b5e5e-91fe-4dd5-b41d-022467f6eefd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassCohomologousAlongEndomorphism
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EndClass
variable {X Y Z T : Scheme.{0}}
namespace GlobalTheory.KS.EndClass
theorem _root_.solution (O : Y.Opens) {O' : Y.Opens} (h : O' ≤ O) {V : O.toScheme.Opens} (hV : V = O.ι ⁻¹ᵁ O') :
    Function.Bijective (fun s : Γ(Y, O') => pbT O.ι s V) := by
  subst hV
  have e : O.ι ''ᵁ (O.ι ⁻¹ᵁ O') = O' := by
    apply le_antisymm
    · exact Set.image_preimage_subset _ _
    · intro x hx
      exact ⟨⟨x, h hx⟩, hx, rfl⟩
  have key : (fun s : Γ(Y, O') => pbT O.ι s (O.ι ⁻¹ᵁ O')) = (O.ι.appLE O' _ le_rfl).hom := by
    funext s
    simp only [pbT, dif_pos (le_refl (O.ι ⁻¹ᵁ O'))]
  rw [key, Scheme.Opens.ι_appLE]
  rw [show homOfLE (x := O.ι ''ᵁ O.ι ⁻¹ᵁ O') (Set.image_subset_iff.mpr le_rfl) = eqToHom e from Subsingleton.elim _ _]
  rw [eqToHom_op, eqToHom_map]
  have hI : ∀ {A B : CommRingCat} (p : A = B), Function.Bijective (eqToHom p).hom := by
    intro A B p
    subst p
    simpa using Function.bijective_id
  exact hI _
end GlobalTheory.KS.EndClass
