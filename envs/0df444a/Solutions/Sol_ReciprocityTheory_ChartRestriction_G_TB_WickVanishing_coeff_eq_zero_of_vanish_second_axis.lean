-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_second_axis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:38.67285+00:00
-- url     : https://prove2.me/submissions/47204448-1039-4579-a1ff-7b082b1b85ec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_zero_right

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
theorem _root_.solution (h : PS k 2 d) (hax : ev (n := 1) ![pt k d 0, 0] h = 0)
    (m : Fin 2 × Fin d →₀ ℕ) (hm : ∀ i, m (1, i) = 0) : coeff m h = 0 := by
  have hsupp : ↑m.support ⊆ Set.range (eXv d) := by
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hab
    fin_cases a
    · exact ⟨(0, b), rfl⟩
    · exact absurd (hm b) hab
  rw [← Finsupp.embDomain_comapDomain hsupp, ← coeff_ev_zero_right, hax]
  simp
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
