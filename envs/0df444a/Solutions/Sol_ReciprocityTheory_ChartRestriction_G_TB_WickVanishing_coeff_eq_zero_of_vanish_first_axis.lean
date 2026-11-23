-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:07.046452+00:00
-- url     : https://prove2.me/submissions/a12fbfe8-c243-4835-9bc1-7f938e5b7e2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_zero_left

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
theorem _root_.solution (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0)
    (m : Fin 2 × Fin d →₀ ℕ) (hm : ∀ i, m (0, i) = 0) : coeff m h = 0 := by
  have hsupp : ↑m.support ⊆ Set.range (eZ d) := by
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hab
    fin_cases a
    · exact absurd (hm b) hab
    · exact ⟨(0, b), rfl⟩
  rw [← Finsupp.embDomain_comapDomain hsupp, ← coeff_ev_zero_left, hax]
  simp
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
