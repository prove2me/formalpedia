-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_ptm_one__a_64b806b6d605
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:25.061804+00:00
-- url     : https://prove2.me/submissions/2c45a2b8-6a3b-442d-b29b-8e00acdce364

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GmHomAt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_sA_ptm
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_j__eq_fd4b82769420


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
theorem _root_.solution (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (m : ℕ) (k : 𝓞 E) :
    homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c k)) ≫ homAt y.x (jφ φ m) = ptm C ![φa c φ k] m := by
  rw [jφ_eq, sA_ptm C ![φ] (fun i j => by rw [Fin.fin_one_eq_zero i]; exact hφ j) m k]
  refine congrArg (fun P => ptm C P m) (funext fun i => funext fun j => ?_)
  rw [Fin.fin_one_eq_zero i]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
