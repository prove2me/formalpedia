-- Prove2me | solution 1 for P2M_GlobalTheory_GermExist_unit_comp_prim__a51190ddb949
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:17.231413+00:00
-- url     : https://prove2.me/submissions/6289cc5d-2c1f-472b-8bb3-595bae9df8df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TopLePreimageWchart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GermExist
namespace GlobalTheory.GermExist
theorem _root_.solution {S : Scheme.{0}} {A : Over S} [GrpObj A] (w : A ⟶ A) (hw : η[A] ≫ w = η[A])
    (k : Fin 5) : η[A].left ≫ primφ w k = η[A].left := by
  have h1 : η[A] ≫ (1 : A ⟶ A) = η[A] := by
    rw [MonObj.comp_one, Hom.one_def]
    simp
  have h2 : η[A] ≫ (𝟙 A * w : A ⟶ A) = η[A] := by
    rw [MonObj.comp_mul, hw, Category.comp_id]
    have : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by
      rw [Hom.one_def]; simp
    rw [this, _root_.mul_one]
  fin_cases k
  · exact Category.comp_id _
  · exact congrArg (·.left) h2
  · exact Category.comp_id _
  · exact congrArg (·.left) hw
  · exact congrArg (·.left) h1
end GlobalTheory.GermExist
