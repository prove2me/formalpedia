-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.degree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:28:42.326195+00:00
-- url     : https://prove2.me/submissions/00250297-7609-4793-971f-64aa128f248f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution {σ : Type} {e : σ →₀ ℕ} (he : e.degree = 1) :
    ∃ b, e = Finsupp.single b 1 := by
  classical
  have hd : ∑ i ∈ e.support, e i = 1 := by
    first
    | exact he
    | simpa [Finsupp.degree] using he
  have hne : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hd
    exact zero_ne_one hd
  obtain ⟨b, hb⟩ := hne
  refine ⟨b, ?_⟩
  rw [← Finset.add_sum_erase _ _ hb] at hd
  have hb1 : 1 ≤ e b := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hb)
  have hrest : ∑ i ∈ e.support.erase b, e i = 0 := by omega
  have heb : e b = 1 := by omega
  ext i
  by_cases hi : i = b
  · rw [hi, heb, Finsupp.single_eq_same]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    by_cases his : i ∈ e.support
    · exact (Finset.sum_eq_zero_iff.mp hrest) i (Finset.mem_erase.mpr ⟨hi, his⟩)
    · by_contra hc
      exact his (Finsupp.mem_support_iff.mpr hc)
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
