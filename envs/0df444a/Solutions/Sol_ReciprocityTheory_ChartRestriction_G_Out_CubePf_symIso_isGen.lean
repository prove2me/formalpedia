-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.symIso_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:23:30.758444+00:00
-- url     : https://prove2.me/submissions/0d97fc3a-42a9-4d14-8180-b90676f198aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_SubAddEqZeroOfEqAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_mul_inv_mul_cancel_comm
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_inv_comm
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
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
theorem _root_.solution (L : LB G.left) (w₀ : LB.Iso L (L.pull (GrpObj.inv (X := G)).left))
    (hw₀ : w₀.IsGen) : (symIso m L w₀).IsGen := by
  intro p p'
  apply unit_ext
  intro y hy
  have hz : m.F.base y ∈ (LB.div (L.pull (GrpObj.inv (X := G)).left) L).U
        ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit) ⊓
      (LB.div (L.pull (GrpObj.inv (X := G)).left) L).U
        ((fun _ => p'.1 PUnit.unit PUnit.unit), p'.2 PUnit.unit) :=
    ⟨symLe m L p hy.1, symLe m L p' hy.2⟩
  have h0 := congrArg (gU (m.F.base y) hz)
    (hw₀ ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit)
      ((fun _ => p'.1 PUnit.unit PUnit.unit), p'.2 PUnit.unit))
  rw [map_mul, gU_res, gU_res] at h0
  first
  | rw [germ_div _ _ _ _ (m.F.base y) hz] at h0
  | simp only [germ_div] at h0
  rw [map_mul, gU_res, gU_res]
  first
  | rw [germ_div _ _ p p' y hy]
  | simp only [germ_div]
  apply mul_inv_mul_cancel_comm (Units.map (m.F.stalkMap y).hom) _ _ _ _ _ _ _ _ h0
  · dsimp only [symIso]
    rw [gU_res, gU_pullU]
  · dsimp only [symIso]
    rw [gU_res, gU_pullU]
  · have hmem3 : (GrpObj.inv (X := G)).left.base (m.F.base y) ∈
        L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit) :=
      ⟨LB.wchart_le L (fun _ : PUnit => (GrpObj.inv (X := G)).left)
          (fun _ => p.1 PUnit.unit PUnit.unit) PUnit.unit hz.1.1,
        LB.wchart_le L (fun _ : PUnit => (GrpObj.inv (X := G)).left)
          (fun _ => p'.1 PUnit.unit PUnit.unit) PUnit.unit hz.2.1⟩
    have hmem1 : m.F.base ((GrpObj.inv (X := G')).left.base y) ∈
        L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit) := by
      rw [base_eq (inv_comm m) y]
      exact hmem3
    refine (germ_pull_pull L m.F (GrpObj.inv (X := G')).left p.1 p'.1 y _ hmem1).trans
      ((gU_pullU_congr (inv_comm m) (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) (L.g (p.1 PUnit.unit PUnit.unit) (p'.1 PUnit.unit PUnit.unit)) y hmem1 hmem3).trans
      ((congrArg (gU (O := (m.F ≫ (GrpObj.inv (X := G)).left) ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit))) y hmem3)
          (pullU_comp_lemma m.F (GrpObj.inv (X := G)).left (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) (L.g (p.1 PUnit.unit PUnit.unit) (p'.1 PUnit.unit PUnit.unit)))).trans
      ((gU_pullU m.F ((GrpObj.inv (X := G)).left ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit))) y hmem3 (pullU (GrpObj.inv (X := G)).left (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) (L.g (p.1 PUnit.unit PUnit.unit) (p'.1 PUnit.unit PUnit.unit)))).trans
      ?_)))
    congr 1
    exact (germ_pull L (GrpObj.inv (X := G)).left (fun _ => p.1 PUnit.unit PUnit.unit)
      (fun _ => p'.1 PUnit.unit PUnit.unit) (m.F.base y)
      (⟨hz.1.1, hz.2.1⟩ : m.F.base y ∈
        (L.pull (GrpObj.inv (X := G)).left).U (fun _ => p.1 PUnit.unit PUnit.unit) ⊓
        (L.pull (GrpObj.inv (X := G)).left).U (fun _ => p'.1 PUnit.unit PUnit.unit))
      hmem3).symm
  · exact (germ_pull L m.F p.2 p'.2 y _
      (show m.F.base y ∈ L.U (p.2 PUnit.unit) ⊓ L.U (p'.2 PUnit.unit) from ⟨hz.1.2, hz.2.2⟩)).trans
      (gU_pullU _ _ _ _ _)
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
