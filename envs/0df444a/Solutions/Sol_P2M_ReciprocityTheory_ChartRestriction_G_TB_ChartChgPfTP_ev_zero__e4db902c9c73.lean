-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_TB_ChartChgPfTP_ev_zero__e4db902c9c73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:13:25.441915+00:00
-- url     : https://prove2.me/submissions/4d9c41d6-8633-4847-9b0a-9078a5df68cd

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
theorem _root_.solution {m n : ℕ} {a : Fin m → Pt k n d} (ha : ∀ p q, constantCoeff (a p q) = 0) :
    ev a (0 : PS k m d) = 0 := by
  have hs := ChartChgPfTP.hasSubst_ev ha
  have e : ∀ f : PS k m d, ev a f = MvPowerSeries.substAlgHom hs f := fun f => by
    first
    | rfl
    | (rw [MvPowerSeries.coe_substAlgHom]; rfl)
    | simp [MvPowerSeries.coe_substAlgHom, ev]
  rw [e, map_zero]
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
