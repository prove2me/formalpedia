-- Prove2me | solution 1 for P2M_GlobalTheory_JetSer_FrameChange_cub_lam__899c0adc3157
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:31:48.063832+00:00
-- url     : https://prove2.me/submissions/58601204-84b2-46e3-862b-0c74bbdb5818

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub


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
variable [IsCommMonObj G]
namespace GlobalTheory.JetSer.FrameChange
theorem _root_.solution {T : Over S} (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) (t : U) :
    t * lamV h x (x' * y) =
      (∏ I : thK, h ((lift x (lift x' y)).left ≫ thφ G (x3 G) I) ^ thε I) * t * (lamV h x x' * lamV h x y) := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.prod_cub]
  simp only [lamV, ← _root_.mul_assoc x x' y]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.JetSer.FrameChange
