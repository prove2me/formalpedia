-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_res_eq_of_res_eq__709669c04f21
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:28.669801+00:00
-- url     : https://prove2.me/submissions/0e4f07cb-1eb0-43c6-934e-931d9f93cdde

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ResEqOfResEq

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
open ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
variable {X Y Z W : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
theorem _root_.solution {U V W : Y.Opens} (a : Γ(Y, U)ˣ) (b : Γ(Y, V)ˣ) (h1 : W ≤ U) (h2 : W ≤ V)
    (h : res (inf_le_left : U ⊓ V ≤ U) a = res (inf_le_right : U ⊓ V ≤ V) b) :
    res h1 a = res h2 b := by
  have hW : W ≤ U ⊓ V := le_inf h1 h2
  have key : ∀ {P : Y.Opens} (hP : U ⊓ V ≤ P) (hQ : W ≤ P) (c : Γ(Y, P)ˣ),
      res hQ c = res hW (res hP c) := by
    intro P hP hQ c
    have e : Y.presheaf.map (homOfLE hQ).op =
        Y.presheaf.map (homOfLE hP).op ≫ Y.presheaf.map (homOfLE hW).op := by
      rw [← Functor.map_comp]
      rfl
    ext
    exact congrArg (fun φ => φ.hom c.val) e
  rw [key inf_le_left h1 a, key inf_le_right h2 b, h]
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
