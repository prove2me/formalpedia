-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ev_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:37.635996+00:00
-- url     : https://prove2.me/submissions/c5a30976-a758-4de8-8482-dd131c669017

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
theorem _root_.solution {m n r : ℕ} (a : Fin m → Pt k n d) (b : Fin n → Pt k r d) (ha : ∀ p q, constantCoeff (a p q) = 0)
    (hb : ∀ p q, constantCoeff (b p q) = 0) (f : PS k m d) :
    ev b (ev a f) = ev (fun p q => ev b (a p q)) f := by
  first
  | exact MvPowerSeries.subst_comp_subst_apply (ChartChgPfTP.hasSubst_ev ha) (ChartChgPfTP.hasSubst_ev hb) f
  | (unfold ev; rw [MvPowerSeries.subst_comp_subst_apply (ChartChgPfTP.hasSubst_ev ha) (ChartChgPfTP.hasSubst_ev hb)])
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
