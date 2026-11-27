-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ev_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:48.780567+00:00
-- url     : https://prove2.me/submissions/3a2e39ee-bf37-4def-a554-f45656f84965

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_hasSubst_ev

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
variable {k : Type} [CommRing k]
variable {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
theorem _root_.solution {m n : ℕ} {a : Fin m → Pt k n d} (ha : ∀ p q, constantCoeff (a p q) = 0) {ι : Type}
    (s : Finset ι) (f : ι → PS k m d) : ev a (∑ i ∈ s, f i) = ∑ i ∈ s, ev a (f i) := by
  have hs := ChartChgPfTP.hasSubst_ev ha
  have e : ∀ f : PS k m d, ev a f = MvPowerSeries.substAlgHom hs f := fun f => by
    first
    | rfl
    | (rw [MvPowerSeries.coe_substAlgHom]; rfl)
    | simp [MvPowerSeries.coe_substAlgHom, ev]
  rw [e, map_sum]
  exact Finset.sum_congr rfl fun i _ => (e (f i)).symm
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
