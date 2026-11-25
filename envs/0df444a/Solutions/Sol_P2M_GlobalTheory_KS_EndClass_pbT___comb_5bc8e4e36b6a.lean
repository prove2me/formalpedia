-- Prove2me | solution 1 for P2M_GlobalTheory_KS_EndClass_pbT___comb_5bc8e4e36b6a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:53:52.805081+00:00
-- url     : https://prove2.me/submissions/b292fab4-8a96-4cad-b910-be49e30541a4

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
import Theorems.Thm_GlobalTheory_KS_EndClass_pbT_pbT
import Theorems.Thm_P2M_GlobalTheory_KS_EndClass_pre___eq_20bc979cb662
import Theorems.Thm_GlobalTheory_KS_InvField_pbT_pbT
import Theorems.Thm_GlobalTheory_KS_InvHom_pbT_pbT
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
namespace GlobalTheory.KS.EndClass
variable {X Y Z T : Scheme.{0}}
private lemma rsT_eq_pbT_id {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) :
    rsT s O = pbT (𝟙 Y) s O := by
  by_cases h : O ≤ O₀
  · have h' : O ≤ (𝟙 Y) ⁻¹ᵁ O₀ := h
    simp only [rsT, pbT, dif_pos h, dif_pos h', Scheme.Hom.appLE, resG]
    rfl
  · have h' : ¬ O ≤ (𝟙 Y) ⁻¹ᵁ O₀ := h
    simp only [rsT, pbT, dif_neg h, dif_neg h']
private lemma pbT_eq_appLE_hom {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {V : Z.Opens} (h : V ≤ f ⁻¹ᵁ O₀)
    (s : Γ(Y, O₀)) : pbT f s V = (f.appLE O₀ V h).hom s := by
  simp only [pbT, dif_pos h]
variable {K : Type} [Field K] {R : Type} [CommRing R] {g : ℕ}
end GlobalTheory.KS.EndClass
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EndClass
variable {X Y Z T : Scheme.{0}}
variable {K : Type} [Field K] {R : Type} [CommRing R] {g : ℕ}
namespace GlobalTheory.KS.EndClass
theorem _root_.solution {m : Y ⟶ X} (dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) (y : Z ⟶ Y) (O : Z.Opens)
    {W₀ W : X.Opens} (hO : O ≤ y ⁻¹ᵁ m ⁻¹ᵁ W₀) (hW : W ≤ W₀) (c : Fin g → Γ(Z, O)) (f : Γ(X, W)) :
    pbT O.ι (∑ a, rsT (c a) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W))
      (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W) =
    ∑ a, rsT (pbT O.ι (c a) (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀)) _ * pbT (O.ι ≫ y) (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
  have hL : ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W ≤ O.ι ⁻¹ᵁ (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) := le_of_eq (pre_ι_eq O y m W)
  have hL₀ : ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W ≤ ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀ := Scheme.Hom.preimage_mono _ hW
  rw [pbT_eq_appLE_hom _ hL, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_mul, ← pbT_eq_appLE_hom _ hL, ← pbT_eq_appLE_hom _ hL]
  congr 1
  · have h₁ : O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W ≤ (𝟙 Z) ⁻¹ᵁ O := inf_le_left
    have h₂ : ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀ ≤ O.ι ⁻¹ᵁ O := by
      rw [Scheme.Opens.ι_preimage_self]
      exact le_top
    have h₃ : ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W ≤ (𝟙 O.toScheme) ⁻¹ᵁ (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀) := hL₀
    rw [rsT_eq_pbT_id, rsT_eq_pbT_id, pbT_pbT O.ι (𝟙 Z) h₁ hL, pbT_pbT (𝟙 O.toScheme) O.ι h₂ h₃]
    simp only [Category.comp_id, Category.id_comp]
  · exact pbT_pbT _ _ inf_le_right hL _
end GlobalTheory.KS.EndClass
