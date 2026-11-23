-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_subst_sum__259da4521e82
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:04.0864+00:00
-- url     : https://prove2.me/submissions/75026d32-5b90-4830-b7db-c9fd81003ebb

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
theorem _root_.solution {σ τ : Type} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) {ι : Type} (s : Finset ι)
    (g : ι → MvPowerSeries σ S) : subst a (∑ i ∈ s, g i) = ∑ i ∈ s, subst a (g i) := by
  first
  | (rw [← coe_substAlgHom ha, map_sum])
  | (induction s using Finset.cons_induction with
      | empty => simp [← coe_substAlgHom ha]
      | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, ← ih, ← coe_substAlgHom ha, map_add])
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
