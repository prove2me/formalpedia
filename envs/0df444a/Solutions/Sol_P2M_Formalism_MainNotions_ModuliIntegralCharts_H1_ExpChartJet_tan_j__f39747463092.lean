-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_tan_j__f39747463092
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:50:28.347557+00:00
-- url     : https://prove2.me/submissions/f81aef28-e9c4-4b36-b01c-8a588d96dbbc

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_jetTan_eq_tp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
variable (C : ChartAt Xo c y)
variable (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
theorem _root_.solution (hφ : IsExpOf C.B.G.F C.uvec φ) (j : Fin (dL Dw)) :
    (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S).comp (jφ φ (0 + 1)) =
      tp (fun q : Fin 1 × Fin C.d => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ q.2)) := by
  apply jet_hom_ext
  intro q
  rw [AlgHom.comp_apply, jφ, jetSubstPS_mk (0 + 1) (fun p : Fin 1 × Fin C.d => φ p.2) (fun p => hφ.const p.2),
    jetTan_eq_tp, tp_psJet, tp_mk, hφ.const, TrivSqZeroExt.inl_zero, zero_add]
  simp only [ite_mul, _root_.one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
