-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_eq_zero_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:18:34.022002+00:00
-- url     : https://prove2.me/submissions/d1f33529-c142-4be4-aad2-f75f2ffdaa41

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
open ReciprocityTheory.PGsh PowerSeries
noncomputable section
variable {K : Type*} [Field K]

theorem solution [IsAlgClosed K] [CharZero K] (lg : PowerSeries K) (M : ℕ)
    (hM : 2 ≤ M) (h : ∀ z : K, z ^ (M - 1) = 1 → rescale z lg = z • lg) (j : ℕ)
    (hj2 : 2 ≤ j) (hj : j < M) : coeff j lg = 0 := by
  have hpos : M - 1 ≠ 0 :=
    ne_of_gt (Nat.sub_pos_of_lt ((one_le_two.trans hj2).trans_lt hj))
  haveI : NeZero ((M - 1 : ℕ) : K) := ⟨Nat.cast_ne_zero.mpr hpos⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (M - 1)
  have hcoeff : ζ ^ j * coeff j lg = ζ * coeff j lg := by
    have := congrArg (coeff j) (h ζ hζ.pow_eq_one)
    simpa [coeff_rescale, smul_eq_mul] using this
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpos
  have hne : ζ ^ j ≠ ζ := by
    intro heq
    have : ζ ^ (j - 1) = 1 := by
      apply mul_left_cancel₀ hζ0
      rw [← pow_succ', Nat.sub_add_cancel (one_le_two.trans hj2), heq, mul_one]
    have hdiv : M - 1 ∣ j - 1 := (hζ.pow_eq_one_iff_dvd (j - 1)).mp this
    have hlt : j - 1 < M - 1 := Nat.sub_lt_sub_right (one_le_two.trans hj2) hj
    have hne0 : j - 1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr (Nat.succ_le_iff.mp hj2)
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hne0) hlt hdiv
  have : (ζ ^ j - ζ) * coeff j lg = 0 := by
    rw [sub_mul, hcoeff, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
