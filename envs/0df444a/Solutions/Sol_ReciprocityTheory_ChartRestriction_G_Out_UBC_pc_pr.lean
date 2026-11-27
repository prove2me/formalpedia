-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.UBC.pc_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:13.18865+00:00
-- url     : https://prove2.me/submissions/240a3c59-b739-4062-a880-07169498c07a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullbackDegree_EpsPullbackFst

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
theorem _root_.solution (φ : R →+* R') {A : Over (Spec (CommRingCat.of R))}
    (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A) :
    (pc φ x).left ≫ pF φ A = specOf φ ≫ x.left := by
  rw [pF_eq]
  have hsymm : (((Over.mapPullbackAdj (specOf φ)).homEquiv _ A).symm (pc φ x)).left =
      (pc φ x).left ≫ pullback.fst A.hom (specOf φ) := rfl
  rw [← hsymm]
  simp only [pc, Equiv.symm_apply_apply, Over.comp_left]
  congr 1
end ReciprocityTheory.ChartRestriction.G.Out.UBC
