-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG__a_one_6e26593e29be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:31:32.047798+00:00
-- url     : https://prove2.me/submissions/d00f5dbf-b5b9-4f3a-b369-7cddc0b7c742

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_UnitIdSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS

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
theorem _root_.solution {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) : φa c φ 1 = φ := by
  have e : actPS (Dw := Dw) (S := S) c 1 = MvPowerSeries.X := by
    funext q
    simp [actPS]
  funext j
  simp only [φa, e, subst_self, id]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
