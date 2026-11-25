-- Prove2me | solution 1 for P2M_GlobalTheory_IsoDesc_exists_lift__24f218a0e0ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:07.822969+00:00
-- url     : https://prove2.me/submissions/f442438f-7dd1-4a30-89c0-5a1791037f48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_GlobalTheory_IsoDesc_exists_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B' : Over S'} {B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj B']
  [IsCommMonObj B'] [GrpObj B] [IsCommMonObj B] {P : CP G} {M' : CP B'} {M : CP B} {q : G ⟶ B'}
  {β : B'.left ⟶ B.left} {hβ : β ≫ B.hom = B'.hom ≫ f}
namespace GlobalTheory.IsoDesc
theorem _root_.solution [Flat q.left] [Surjective q.left] {T : Over S'} (x y u : T ⟶ B') :
    ∃ (T' : Over S') (ρ : T' ⟶ T) (x' y' u' : T' ⟶ G), Flat ρ.left ∧ Surjective ρ.left ∧ x' ≫ q = ρ ≫ x ∧
      y' ≫ q = ρ ≫ y ∧ u' ≫ q = ρ ≫ u := by
  obtain ⟨T₁, ρ₁, x₁, _, _, e₁⟩ := exists_lift (q := q) x
  obtain ⟨T₂, ρ₂, y₂, _, _, e₂⟩ := exists_lift (q := q) (ρ₁ ≫ y)
  obtain ⟨T₃, ρ₃, u₃, _, _, e₃⟩ := exists_lift (q := q) (ρ₂ ≫ ρ₁ ≫ u)
  refine ⟨T₃, ρ₃ ≫ ρ₂ ≫ ρ₁, ρ₃ ≫ ρ₂ ≫ x₁, ρ₃ ≫ y₂, u₃, inferInstanceAs (Flat (ρ₃.left ≫ ρ₂.left ≫ ρ₁.left)),
    inferInstanceAs (Surjective (ρ₃.left ≫ ρ₂.left ≫ ρ₁.left)), ?_, ?_, ?_⟩ <;> simp [*]
end GlobalTheory.IsoDesc
