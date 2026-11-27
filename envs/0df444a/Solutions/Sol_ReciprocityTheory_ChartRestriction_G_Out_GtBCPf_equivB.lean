-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.equivB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:07:30.705802+00:00
-- url     : https://prove2.me/submissions/bbada604-25f1-4617-a4f6-981195a03803

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitsEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_equivPullL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_charUnit_hTB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_bm_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_bm_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_bm_act

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
attribute [local instance] SplitExt.free SplitExt.finite
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S) {G : Over S} [GrpObj G] (d : E.GtDatum G)
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution : ∀ (j : (pullExt f E).ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ (pullExt f E).X),
    res (actB_le f E d j)
        (pullU (lift (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G) ≫ iB f E.X d.i)
          (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)) ≫
            μ[(Over.pullback f).obj G]).left _ (uB f E d j k)) =
      res (fun x _ => show (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left.base x ∈
          (⊤ : TopologicalSpace.Opens _) from trivial)
          (pullU (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left ⊤
            (charUnit S' (pullExt f E).X ((pullExt f E).basis k))) *
        pullU (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left _ (uB f E d j k) := by
  intro j k
  exact equivPullL (act₁ := (lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ[G]).left)
    (s₁ := (snd (splitTorus S E.X) G).left) (f₁ := (fst (splitTorus S E.X) G).left)
    (act₂ := (lift (fst (splitTorus S' E.X) ((Over.pullback f).obj G) ≫ iB f E.X d.i)
          (snd (splitTorus S' E.X) ((Over.pullback f).obj G)) ≫ μ[(Over.pullback f).obj G]).left)
    (s₂ := (snd (splitTorus S' E.X) ((Over.pullback f).obj G)).left)
    (f₂ := (fst (splitTorus S' E.X) ((Over.pullback f).obj G)).left)
    (b := bm f E.X) (a := pullback.fst G.hom f) (h := hT f E.X)
    (W := d.q.left ⁻¹ᵁ E.chart (jj f E j)) (u := d.u (jj f E j) k)
    (W' := (qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) (hW' := pre_le f E d j)
    (c := charUnit S E.X (E.basis k)) (c' := charUnit S' E.X (E.basis k))
    (hc := charUnit_hTB f E.X (E.basis k))
    (le₁ := d.act_le (jj f E j)) (t₁ := fun x _ => trivial)
    (H := d.equiv (jj f E j) k)
    (ha := bm_act f E.X d.i) (hs := bm_snd f E.X) (hf := bm_fst f E.X)
    (le₂ := actB_le f E d j) (t₂ := fun x _ => trivial)
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
