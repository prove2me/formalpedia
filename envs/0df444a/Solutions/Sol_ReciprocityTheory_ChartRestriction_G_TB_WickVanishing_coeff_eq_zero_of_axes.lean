-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_axes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:41:08.979888+00:00
-- url     : https://prove2.me/submissions/cf2ccbf7-3fdf-4595-8c65-56c0c3540c5b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_eq_zero_of_vanish_first_axis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_eq_zero_of_vanish_second_axis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_two_le_degree

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (h : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] h = 0)
    (h1 : ev (n := 1) ![pt k d 0, 0] h = 0) (m : Fin 2 × Fin d →₀ ℕ) (hm : m.degree < 2) : coeff m h = 0 := by
  by_cases hA : ∀ i, m (0, i) = 0
  · exact coeff_eq_zero_of_vanish_first_axis h h0 m hA
  by_cases hB : ∀ i, m (1, i) = 0
  · exact coeff_eq_zero_of_vanish_second_axis h h1 m hB
  push_neg at hA hB
  obtain ⟨i, hi⟩ := hA
  obtain ⟨i', hi'⟩ := hB
  have := two_le_degree hi hi'
  omega
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
