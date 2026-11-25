-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.two_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:33:06.516823+00:00
-- url     : https://prove2.me/submissions/63abb1bd-8a41-4e0a-990d-0e0dc8ce3f74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum

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
theorem _root_.solution {m : Fin 2 × Fin d →₀ ℕ} {i i' : Fin d} (h0 : m (0, i) ≠ 0) (h1 : m (1, i') ≠ 0) :
    2 ≤ m.degree := by
  classical
  have hne : ((0 : Fin 2), i) ≠ ((1 : Fin 2), i') := by simp
  have hs : ({((0 : Fin 2), i), ((1 : Fin 2), i')} : Finset (Fin 2 × Fin d)) ⊆ m.support := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  have h2 : m (0, i) + m (1, i') ≤ ∑ x ∈ m.support, m x := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset hs
  have hdeg : m.degree = ∑ x ∈ m.support, m x := by
    unfold Finsupp.degree
    rfl
  omega
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
