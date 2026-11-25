-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ordGE_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:31:32.798697+00:00
-- url     : https://prove2.me/submissions/cd734640-8afc-44fa-ad1f-66b98eebcf6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP

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
namespace ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
theorem _root_.solution {σ : Type} {r : ℕ} (i : σ) {g : MvPowerSeries σ k} (h : OrdGE (r + 1) g) :
    OrdGE r (pderiv k i g) := by
  intro e he
  have key : coeff (e + Finsupp.single i 1) g = 0 := h _ (by
    first
    | (rw [map_add, Finsupp.degree_single]; omega)
    | (simp; omega)
    | (simp [map_add]; omega))
  have key' : coeff (Finsupp.single i 1 + e) g = 0 := by rw [add_comm]; exact key
  first
  | (rw [MvPowerSeries.coeff_pderiv, key, mul_zero])
  | (rw [MvPowerSeries.coeff_pderiv, key, zero_mul])
  | simp [MvPowerSeries.coeff_pderiv, key, key']
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
