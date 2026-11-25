-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG__a_mul_3f365165b132
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:41:23.775063+00:00
-- url     : https://prove2.me/submissions/7636b506-8483-4acc-a4c1-e727951b721f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_UnitIdSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_hasSubst_actPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_actPS_comp

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
open MvPowerSeries NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
theorem _root_.solution {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (u v : 𝓞 E) (j : Fin d) :
    subst (actPS (Dw := Dw) c v) (φa c φ u j) = φa c φ (u * v) j := by
  simp only [φa]
  rw [subst_comp_subst_apply (hasSubst_actPS c u) (hasSubst_actPS c v)]
  congr 1
  funext q
  exact actPS_comp c u v q
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
