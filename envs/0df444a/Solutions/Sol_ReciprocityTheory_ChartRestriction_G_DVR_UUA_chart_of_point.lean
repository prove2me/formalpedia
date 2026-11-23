-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.UUA.chart_of_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:20.469315+00:00
-- url     : https://prove2.me/submissions/eb762653-0624-424a-98af-a14e059bdc57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LiftOUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ChartOfPoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_gs_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (h : ∀ y I, Good L y I → sval s (𝟙 Y) y I = ∑ i, gs (𝟙 Y) y ⊤ (b i) * sval (t i) (𝟙 Y) y I) :
    ∀ j, s.f j = ∑ i, resTop _ (b i) * (t i).f j := by
  intro j
  refine fn_ext fun y hy0 => ?_
  have hy : y ∈ LB.wchart L φ j := hy0
  choose I hI using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
  have hIy : Good L y I := hI
  have mm := hIy.mem φ (𝟙 _)
  have T0 := sec_trans s (𝟙 _) y hy mm
  set τ := (trF φ ε (𝟙 _) y j (fun k => I (𝟙 _ ≫ φ k))).val with hτ
  have RHS : gs (𝟙 _) y (LB.wchart L φ j) (∑ i, resTop (LB.wchart L φ j) (b i) *
      (show Γ(Y, LB.wchart L φ j) from (t i).f j)) =
      τ * ∑ i, gs (𝟙 _) y ⊤ (b i) * sval (t i) (𝟙 _) y I := by
    rw [gs_sum _ y _ hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul _ y _ hy, gs_res _ y le_top hy, sec_trans (t i) (𝟙 _) y hy mm, hτ]
    exact mul_left_comm _ _ _
  exact T0.trans ((congrArg (fun x => τ * x) (h y I hIy)).trans RHS.symm)
end ReciprocityTheory.ChartRestriction.G.DVR.UUA
