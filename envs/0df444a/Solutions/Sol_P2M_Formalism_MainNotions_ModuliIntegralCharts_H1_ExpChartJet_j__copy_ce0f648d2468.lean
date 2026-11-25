-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_j__copy_ce0f648d2468
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:31:14.325275+00:00
-- url     : https://prove2.me/submissions/d2b1c466-4e12-4a03-98f6-2100bdea251e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_cc_atPt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetCopy_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
variable (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
theorem _root_.solution (hφ : IsExpOf C.B.G.F C.uvec φ) (m : ℕ) (i : Fin 2) :
    (jetCopy (dL Dw) m i).comp (jφ φ m) =
      (jetSubstPS (m := m) (fun p : Fin 2 × Fin C.d => atPt p.1 (φ p.2))).comp (jetCopy C.d m i) := by
  apply jet_hom_ext
  intro p
  have h1 : (jetCopy (S := S) C.d m i) (Ideal.Quotient.mk _ (MvPolynomial.X p)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, p.2)) := by
    rw [jetCopy, jetMap_mk, MvPolynomial.aeval_X]
  rw [AlgHom.comp_apply, AlgHom.comp_apply, h1, jetSubstPS_mk m (fun p : Fin 2 × Fin C.d => atPt p.1 (φ p.2)) (fun q => cc_atPt q.1 (hφ.const q.2)), jφ,
    jetSubstPS_mk m (fun p : Fin 1 × Fin C.d => φ p.2) (fun q => hφ.const q.2), jetCopy_eq,
    jetSubstPS_psJet m (fun p : Fin 1 × Fin (dL Dw) => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S))
      (fun _ => MvPowerSeries.constantCoeff_X _)]
  all_goals rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
