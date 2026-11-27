-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.UBC.pc_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:08.836794+00:00
-- url     : https://prove2.me/submissions/d48da0b5-434d-4aed-b30b-798ef4449a7d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullbackDegree_EpsPullbackFst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_UBC_homEquiv_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.UBC
open Semi
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
namespace ReciprocityTheory.ChartRestriction.G.Out.UBC
theorem _root_.solution (φ : R →+* R') {A : Over (Spec (CommRingCat.of R))} [GrpObj A] [IsCommMonObj A]
    (x y : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A) :
    pc φ (padd A x y) = padd (pA φ A) (pc φ x) (pc φ y) := by
  simp only [pc, padd]
  have key := homEquiv_mul (specOf φ) (𝟙_ (Over (Spec (CommRingCat.of R')))) A
    (toUnit ((Over.map (specOf φ)).obj (𝟙_ (Over (Spec (CommRingCat.of R'))))) ≫ x)
    (toUnit ((Over.map (specOf φ)).obj (𝟙_ (Over (Spec (CommRingCat.of R'))))) ≫ y)
  rw [← MonObj.comp_mul] at key
  exact key
end ReciprocityTheory.ChartRestriction.G.Out.UBC
