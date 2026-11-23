-- Prove2me | solution 1 for P2M_GlobalTheory_JetSer_FrameChange_lift_lam__1e26ca842b72
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:57.043057+00:00
-- url     : https://prove2.me/submissions/a7814e87-113e-4f29-b4f5-111965b263fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree

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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FrameChange
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
variable {G}
namespace GlobalTheory.JetSer.FrameChange
theorem _root_.solution {T : Over S} (x y : T ⟶ G) (k : Fin 4) :
    (lift x y).left ≫ lamφ G k = ((![x * y, x, y, 1] : Fin 4 → (T ⟶ G)) k).left := by
  have e₀ : lift x y ≫ (fst G G * snd G G) = x * y := (MonObj.comp_mul _ _ _).trans (by simp)
  have e₃ : lift x y ≫ (1 : G ⊗ G ⟶ G) = 1 := MonObj.comp_one _
  fin_cases k
  · exact congrArg (fun q => q.left) e₀
  · exact congrArg (fun q => q.left) (lift_fst x y)
  · exact congrArg (fun q => q.left) (lift_snd x y)
  · exact congrArg (fun q => q.left) e₃
end GlobalTheory.JetSer.FrameChange
