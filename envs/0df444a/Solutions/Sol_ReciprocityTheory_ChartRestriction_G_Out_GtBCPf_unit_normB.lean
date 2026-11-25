-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.unit_normB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:46:04.809918+00:00
-- url     : https://prove2.me/submissions/37be7b3b-e299-464a-a810-eaf772cc55c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullbackDegree_EpsPullbackFst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitNorm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_unit_norm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S)
attribute [local instance] SplitExt.free SplitExt.finite
variable {G : Over S} [GrpObj G] (d : E.GtDatum G)
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution (j : (pullExt f E).ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ (pullExt f E).X) :
    res (inf_le_left : eSec ((Over.pullback f).obj G) ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) ⊓
          (((pullExt f E).O ((pullExt f E).basis k)).L.pull (eSec (pullExt f E).B)).U (fun _ => j k) ≤
          eSec ((Over.pullback f).obj G) ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j))
        (pullU (eSec ((Over.pullback f).obj G)) _ (uB f E d j k)) *
      res (inf_le_right : eSec ((Over.pullback f).obj G) ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) ⊓
          (((pullExt f E).O ((pullExt f E).basis k)).L.pull (eSec (pullExt f E).B)).U (fun _ => j k) ≤
          (((pullExt f E).O ((pullExt f E).basis k)).L.pull (eSec (pullExt f E).B)).U (fun _ => j k))
        (((pullExt f E).O ((pullExt f E).basis k)).rig.s (fun _ => j k)) = 1 := by
  have hmB : (mB f E).e = f := rfl
  have he : eSec ((Over.pullback f).obj G) ≫ pullback.fst G.hom f = (mB f E).e ≫ eSec G := by
    rw [hmB]
    simp [eSec]
    refine (pullback.lift_fst _ _ _).trans ?_
    simpa using (pullback.condition_assoc (f := 𝟙 S) (g := f) η[G].left)
  exact unit_norm_pull (eSec G) (eSec ((Over.pullback f).obj G)) (pullback.fst G.hom f) (mB f E).e he
    (d.u (jj f E j) k) (pre_le f E d j) ((E.O (E.basis k)).rig.s (fun _ => jj f E j k))
    (rigPull_le (mB f E).F (mB f E).e (mB f E).e_comm (E.O (E.basis k)).L (fun _ => j k))
    (d.unit_norm (jj f E j) k)
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
