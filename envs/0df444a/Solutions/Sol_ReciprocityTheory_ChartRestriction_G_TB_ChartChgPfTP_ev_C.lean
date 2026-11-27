-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ev_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:33:27.633894+00:00
-- url     : https://prove2.me/submissions/e1ff16af-56a0-4bbd-b917-89948528f80b

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
theorem _root_.solution {m n : ℕ} {a : Fin m → Pt k n d} (ha : ∀ p q, constantCoeff (a p q) = 0) (c : k) :
    ev a (C c : PS k m d) = C c := by
  have hs := ChartChgPfTP.hasSubst_ev ha
  have e : ∀ f : PS k m d, ev a f = MvPowerSeries.substAlgHom hs f := fun f => by
    first
    | rfl
    | (rw [MvPowerSeries.coe_substAlgHom]; rfl)
    | simp [MvPowerSeries.coe_substAlgHom, ev]
  rw [e, show (C c : PS k m d) = c • (1 : PS k m d) by rw [MvPowerSeries.smul_eq_C_mul, mul_one],
    map_smul, map_one, MvPowerSeries.smul_eq_C_mul, mul_one]
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
