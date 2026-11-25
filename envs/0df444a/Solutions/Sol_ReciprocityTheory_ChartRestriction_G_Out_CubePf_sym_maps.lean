-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.sym_maps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:30:41.690791+00:00
-- url     : https://prove2.me/submissions/916f14ee-0df8-442d-904b-928c413b302d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_SubAddEqZeroOfEqAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_gU_pullU_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_sub_add_eq_zero_of_eq_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_gU_linCombIso_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_pt1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_pt2
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_base_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pull_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res pullU_res'
  base_eq germ_pull germ_pull_pull germ_div)
section Sym
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] (m : CubeMap G' G)
private theorem pullU_comp_lemma {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens)
    (x : Γ(X, U)ˣ) : pullU (f ≫ g) U x = pullU f (g ⁻¹ᵁ U) (pullU g U x) := by
  first
  | rfl
  | (ext; simp [pullU])
private theorem gU_pullU_id_lemma_3 {X : Scheme.{0}} (U : X.Opens) (y : X) (hy : y ∈ U)
    (hy' : y ∈ (𝟙 X) ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    gU y hy' (pullU (𝟙 X) U u) = gU y hy u :=
  gU_pullU_id U y hy' u
end Sym
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res pullU_res'
  base_eq germ_pull germ_pull_pull germ_div)
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] (m : CubeMap G' G)
set_option maxHeartbeats 800000
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
theorem _root_.solution (L : RigLB G) (he : eSec G ≫ (GrpObj.inv (X := G)).left = 𝟙 _ ≫ eSec G)
    (w₀ : LB.Iso L.L (L.L.pull (GrpObj.inv (X := G)).left))
    (hm : LB.Gen.Maps (LB.linCombIso w₀ (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L.rig
      (rigPullOf (GrpObj.inv (X := G)).left (𝟙 _) he L.L L.rig)) :
    LB.Gen.Maps (LB.linCombIso (symIso m L.L w₀) (K := PUnit) (fun _ => eSec G') (fun _ => 1))
      (m.rigPull L.L L.rig)
      (rigPullOf (GrpObj.inv (X := G')).left (𝟙 _) (eSec_inv G') (L.L.pull m.F)
        (m.rigPull L.L L.rig)) := by
  intro p
  apply unit_ext
  intro y hy
  have b1 : (eSec G').base y ∈ ((L.L.pull m.F).pull (GrpObj.inv (X := G')).left).U (p.1 PUnit.unit) :=
    LB.wchart_le ((L.L.pull m.F).pull (GrpObj.inv (X := G')).left) (fun _ : PUnit => eSec G') p.1
      PUnit.unit hy.1
  have b2 : (GrpObj.inv (X := G')).left.base ((eSec G').base y) ∈
      (L.L.pull m.F).U (p.1 PUnit.unit PUnit.unit) :=
    LB.wchart_le (L.L.pull m.F) (fun _ : PUnit => (GrpObj.inv (X := G')).left) (p.1 PUnit.unit)
      PUnit.unit b1
  have b3 : m.F.base ((GrpObj.inv (X := G')).left.base ((eSec G').base y)) ∈
      L.L.U (p.1 PUnit.unit PUnit.unit PUnit.unit) :=
    LB.wchart_le L.L (fun _ : PUnit => m.F) (p.1 PUnit.unit PUnit.unit) PUnit.unit b2
  have b4 : (GrpObj.inv (X := G)).left.base ((eSec G).base (m.e.base y)) ∈
      L.L.U (p.1 PUnit.unit PUnit.unit PUnit.unit) := by
    rw [← pt1 m y]
    exact b3
  have c1 : (eSec G').base y ∈ (L.L.pull m.F).U (p.2 PUnit.unit) :=
    LB.wchart_le (L.L.pull m.F) (fun _ : PUnit => eSec G') p.2 PUnit.unit hy.2
  have c2 : m.F.base ((eSec G').base y) ∈ L.L.U (p.2 PUnit.unit PUnit.unit) :=
    LB.wchart_le L.L (fun _ : PUnit => m.F) (p.2 PUnit.unit) PUnit.unit c1
  have c3 : (eSec G).base (m.e.base y) ∈ L.L.U (p.2 PUnit.unit PUnit.unit) := by
    rw [← pt2 m y]
    exact c2
  have d0 : (eSec G).base (m.e.base y) ∈
      (L.L.pull (GrpObj.inv (X := G)).left).U (fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit) ⊓
        L.L.U (p.2 PUnit.unit PUnit.unit) :=
    ⟨memW_lemma_2 L.L (fun _ : PUnit => (GrpObj.inv (X := G)).left)
      (fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit) ((eSec G).base (m.e.base y)) b4, c3⟩
  have d0' : m.e.base y ∈ (eSec G) ⁻¹ᵁ
      (LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit) := d0
  have d1 : y ∈ (eSec G') ⁻¹ᵁ (m.F ⁻¹ᵁ
      (LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) := by
    show m.F.base ((eSec G').base y) ∈
      (L.L.pull (GrpObj.inv (X := G)).left).U (fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit) ⊓
        L.L.U (p.2 PUnit.unit PUnit.unit)
    rw [pt2 m y]
    exact d0
  have hz : m.e.base y ∈
      ((L.L.pull (GrpObj.inv (X := G)).left).pull (eSec G)).U
        (fun _ _ => p.1 PUnit.unit PUnit.unit PUnit.unit) ⊓
      (L.L.pull (eSec G)).U (fun _ => p.2 PUnit.unit PUnit.unit) :=
    ⟨memW_lemma_2 (L.L.pull (GrpObj.inv (X := G)).left) (fun _ : PUnit => eSec G)
        (fun _ _ => p.1 PUnit.unit PUnit.unit PUnit.unit) (m.e.base y) d0.1,
      memW_lemma_2 L.L (fun _ : PUnit => eSec G) (fun _ => p.2 PUnit.unit PUnit.unit) (m.e.base y) c3⟩
  have h0 := congrArg (gU (m.e.base y) hz)
    (hm ((fun _ _ => p.1 PUnit.unit PUnit.unit PUnit.unit), (fun _ => p.2 PUnit.unit PUnit.unit)))
  first
  | rw [id_eq] at h0
  | skip
  rw [map_mul, gU_res, gU_res] at h0
  first
  | rw [id_eq]
  | skip
  rw [map_mul, gU_res, gU_res]
  apply sub_add_eq_zero_of_eq_add (Units.map (m.e.stalkMap y).hom) _ _ _ _ _ _ h0
  · dsimp only [rigPullOf, CubeMap.rigPull]
    refine ((gU_res _ y _ _).trans ((gU_pullU_id _ y _ _).trans ((gU_res _ y _ _).trans
      (gU_pullU m.e _ y _ _)))).trans ?_
    exact (congrArg (Units.map (m.e.stalkMap y).hom.toMonoidHom)
      ((gU_res _ _ _ _).trans (gU_pullU_id_lemma_3 _ _ _ _ _))).symm
  · have hyl : (eSec G').base y ∈ ((L.L.pull m.F).pull (GrpObj.inv (X := G')).left).U (p.1 PUnit.unit) ⊓
        (L.L.pull m.F).U (p.2 PUnit.unit) := ⟨b1, c1⟩
    refine (gU_linCombIso_unit (symIso m L.L w₀) (eSec G') p y _ hyl).trans
      ((gU_pullU_res (eSec G') (symLe m L.L (p.1 PUnit.unit, p.2 PUnit.unit))
          (pullU m.F _ (w₀.s ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit))) y hyl d1).trans
      ((congrArg (gU y d1) (pullU_comp_lemma (eSec G') m.F ((LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) (w₀.s ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)))).symm.trans
      ((gU_pullU_congr m.e_comm ((LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) (w₀.s ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) y d1 d0').trans
      ((congrArg (gU (O := (m.e ≫ eSec G) ⁻¹ᵁ (LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) y d0')
          (pullU_comp_lemma m.e (eSec G) ((LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) (w₀.s ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)))).trans
      ((gU_pullU m.e ((eSec G) ⁻¹ᵁ (LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) y d0' (pullU (eSec G) ((LB.div (L.L.pull (GrpObj.inv (X := G)).left) L.L).U ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)) (w₀.s ((fun _ => p.1 PUnit.unit PUnit.unit PUnit.unit), p.2 PUnit.unit PUnit.unit)))).trans
      ?_)))))
    exact congrArg (Units.map (m.e.stalkMap y).hom.toMonoidHom) (gU_linCombIso_unit w₀ (eSec G)
      ((fun _ _ => p.1 PUnit.unit PUnit.unit PUnit.unit), (fun _ => p.2 PUnit.unit PUnit.unit))
      (m.e.base y) hz d0').symm
  · dsimp only [CubeMap.rigPull, rigPullOf]
    exact (gU_res _ y _ _).trans (gU_pullU m.e _ y _ _)
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
