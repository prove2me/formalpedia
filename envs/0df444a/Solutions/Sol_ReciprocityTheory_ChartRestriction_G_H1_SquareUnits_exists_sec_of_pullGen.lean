-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.SquareUnits.exists_sec_of_pullGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:30.095677+00:00
-- url     : https://prove2.me/submissions/3fa5bbe4-f58e-4140-b7fc-86a2bf88d979

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_UnitAt_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
  CartesianMonoidalCategory MonObj TopologicalSpace Opposite
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
theorem _root_.solution {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y)
    (c : LB.Gen ((LB.LinComb L φ ε).pull h)) (hc : c.IsGen) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε), ∀ (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι),
      Good L z J → IsUnit (sval s r z J) := by
  have l : ∀ j : K → L.ι, LB.wchart L (fun k => h ≫ φ k) j ≤
      LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => h) (fun _ => j) :=
    fun _ _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have e1 : ∀ (j : K → L.ι) (y : Y'), y ∈ LB.wchart L (fun k => h ≫ φ k) j →
      gs (𝟙 Y') y _ (res (l j) (c.s (fun _ => j))).val =
        (gm (𝟙 Y') y (LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => h) (fun _ => j)) (c.s (fun _ => j))).val :=
    fun j y hj => (gs_unit _ y _ hj _).trans (congrArg Units.val (gm_res _ y (l j) hj _))
  refine ⟨⟨fun j => (res (l j) (c.s (fun _ => j))).val, fun j j' => fn_ext fun y hy => ?_⟩, ?_⟩
  · refine ((gs_res (𝟙 Y') y _ hy _).trans (e1 j y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
        (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans
          (e1 j' y hy.2)))).symm)
    have m : ∀ j : K → L.ι, y ∈ LB.wchart L (fun k => h ≫ φ k) j → (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j :=
      fun j hj => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k
    rw [gen_trans hc (𝟙 Y') y (l j hy.1) (l j' hy.2), Units.val_mul]
    congr 2
    simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    exact (gm_linComb L φ ε (𝟙 Y' ≫ h) y j j' (m j hy.1) (m j' hy.2)).trans (by simp only [Category.assoc])
  · intro r z J hJ
    have hm := hJ.mem (fun k => h ≫ φ k) r
    exact (congrArg IsUnit (gs_unit r z _ hm _)).mpr (Units.isUnit _)
end ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
