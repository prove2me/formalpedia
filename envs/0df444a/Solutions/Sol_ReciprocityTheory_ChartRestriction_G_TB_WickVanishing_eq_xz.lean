-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.eq_xz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:33:06.5432+00:00
-- url     : https://prove2.me/submissions/32823301-1737-4010-aa17-7d5ec0e637b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable

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
variable {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {n : Fin 2 × Fin d →₀ ℕ} {l m : Fin d} (h0 : n (0, l) ≠ 0) (h1 : n (1, m) ≠ 0) (hd : n.degree ≤ 2) :
    n = single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), m) 1 := by
  have hne : ((0 : Fin 2), l) ≠ ((1 : Fin 2), m) := by simp
  set u : Fin 2 × Fin d →₀ ℕ := single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), m) 1 with hu
  have hle : u ≤ n := by
    rw [Finsupp.le_def]
    intro x
    simp only [hu, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    by_cases h0x : ((0 : Fin 2), l) = x <;> by_cases h1x : ((1 : Fin 2), m) = x
    · exact absurd (h0x.trans h1x.symm) hne
    · subst h0x
      simp only [if_true, h1x, if_false]
      omega
    · subst h1x
      simp only [if_true, h0x, if_false]
      omega
    · simp [h0x, h1x]
  obtain ⟨w, rfl⟩ : ∃ w, n = u + w := ⟨n - u, (add_tsub_cancel_of_le hle).symm⟩
  have hadd : ∀ a b : Fin 2 × Fin d →₀ ℕ, (a + b).degree = a.degree + b.degree := by
    intro a b
    first
      | exact map_add _ a b
      | simp [Finsupp.degree_eq_weight_one, map_add]
      | simp [Finsupp.degree, Finsupp.sum_add_index']
  have hsg : ∀ x : Fin 2 × Fin d, (single x 1).degree = 1 := by
    intro x
    first
      | exact Finsupp.degree_single x 1
      | simp [Finsupp.degree_eq_weight_one]
      | simp [Finsupp.degree]
  have hdu : u.degree = 2 := by
    rw [hu, hadd, hsg, hsg]
  rw [hadd, hdu] at hd
  have hw : w.degree = 0 := by omega
  rw [Finsupp.degree_eq_zero_iff] at hw
  rw [hw, add_zero]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
