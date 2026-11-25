-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_dAdd_single__5657c32646f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:46:18.686279+00:00
-- url     : https://prove2.me/submissions/a6f3c695-5475-495f-935a-98d4e0926c92

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_dAdd_single

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
open MvPowerSeries
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
theorem _root_.solution {S : Type} [CommRing S] {d n : ℕ} (j : Fin d) (b : Fin n) :
    (TB.dAdd (Pi.single j 1) b : Germ.PS S n d → Germ.PS S n d) = pderiv S (b, j) :=
  funext fun G => dAdd_single j b G
end Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
