-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:53:45.94411+00:00
-- url     : https://prove2.me/submissions/37c63ca5-85f6-4757-9b33-d048e6dfd970

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffAddFirstSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution {n : ℕ} {p q : Pt k n d} (hpq : CZ (![p, q] : Fin 2 → Pt k n d)) (h : PS k 2 d) (v : Fin n × Fin d) :
    pderiv k v (ev (n := n) ![p, q] h) = ∑ c, ev (n := n) ![p, q] (pderiv k ((0 : Fin 2), c) h) * pderiv k v (p c) +
      ∑ c, ev (n := n) ![p, q] (pderiv k ((1 : Fin 2), c) h) * pderiv k v (q c) := by
  rw [pderiv_ev hpq, Fintype.sum_prod_type, Fin.sum_univ_two]
  rfl
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
