-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_nsmul__ee4e35b9e155
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:31:12.693377+00:00
-- url     : https://prove2.me/submissions/7c4d0b7c-eb65-4505-a45f-f72d69fe6c01

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
theorem _root_.solution {σ : Type} (k : ℕ) (g : MvPowerSeries σ S) :
    map ψ ((k : S) • g) = (k : S') • map ψ g := by
  ext n
  simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
