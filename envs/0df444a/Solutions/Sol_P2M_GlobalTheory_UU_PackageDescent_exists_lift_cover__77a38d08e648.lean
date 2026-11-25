-- Prove2me | solution 1 for P2M_GlobalTheory_UU_PackageDescent_exists_lift_cover__77a38d08e648
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:14:04.722191+00:00
-- url     : https://prove2.me/submissions/e6fbc9ee-46bc-47c1-bee6-af4d3add055a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough
import Theorems.Thm_GlobalTheory_UU_PackageDescent_exists_lift_cover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {S : Scheme.{0}} {G B : Over S} (q : G ⟶ B) [Flat q.left] [Surjective q.left]
namespace GlobalTheory.UU.PackageDescent
theorem _root_.solution {T : Over S} (x y u v : T ⟶ B) :
    ∃ (T' : Over S) (ρ : T' ⟶ T) (x' y' u' v' : T' ⟶ G), Flat ρ.left ∧ Surjective ρ.left ∧ x' ≫ q = ρ ≫ x ∧
      y' ≫ q = ρ ≫ y ∧ u' ≫ q = ρ ≫ u ∧ v' ≫ q = ρ ≫ v := by
  obtain ⟨T₁, ρ₁, x', _, _, e₁⟩ := exists_lift_cover q x
  obtain ⟨T₂, ρ₂, y', _, _, e₂⟩ := exists_lift_cover q (ρ₁ ≫ y)
  obtain ⟨T₃, ρ₃, u', _, _, e₃⟩ := exists_lift_cover q (ρ₂ ≫ ρ₁ ≫ u)
  obtain ⟨T₄, ρ₄, v', _, _, e₄⟩ := exists_lift_cover q (ρ₃ ≫ ρ₂ ≫ ρ₁ ≫ v)
  refine ⟨T₄, ρ₄ ≫ ρ₃ ≫ ρ₂ ≫ ρ₁, ρ₄ ≫ ρ₃ ≫ ρ₂ ≫ x', ρ₄ ≫ ρ₃ ≫ y', ρ₄ ≫ u', v', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Over.comp_left]; infer_instance
  · simp only [Over.comp_left]; infer_instance
  all_goals simp only [Category.assoc, e₁, e₂, e₃, e₄]
end GlobalTheory.UU.PackageDescent
