-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ev_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:28.523823+00:00
-- url     : https://prove2.me/submissions/53fb00c8-00cf-4180-b0c7-fb9ffc94493d

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
theorem _root_.solution {m n : ℕ} {a : Fin m → Pt k n d} (ha : ∀ p q, constantCoeff (a p q) = 0) (f g : PS k m d) :
    ev a (f + g) = ev a f + ev a g := by
  first
  | exact MvPowerSeries.subst_add (ChartChgPfTP.hasSubst_ev ha) f g
  | exact map_add (MvPowerSeries.substAlgHom (ChartChgPfTP.hasSubst_ev ha)) f g
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
