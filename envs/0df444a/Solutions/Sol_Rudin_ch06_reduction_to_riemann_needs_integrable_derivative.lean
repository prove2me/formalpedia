-- Prove2me | solution 1 for Rudin.ch06_reduction_to_riemann_needs_integrable_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T19:36:45.2892+00:00
-- url     : https://prove2.me/submissions/bf605498-6afd-49e3-961a-6707d7289c4e

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_ch06_riemann_criterion

/-!
# Rudin, Theorem 6.17: the Riemann integrability of the density cannot be dropped

A Volterra-type construction.  `VolFat.Kset` is `[0,1]` with a small neighbourhood of every
rational removed; it is closed, has empty interior and measure at least `3/4`.  On each
complementary interval `(a,b)` we place the bump
`g a b y = ((y-a)(b-y)/(b-a))^2 * sin (1/(y-a))` of `VolCalc`, which vanishes to second order at
both endpoints and whose derivative oscillates between values close to `-1` and `1` as `y` tends
to `a`.  Adding `2x` produces a strictly increasing `alpha`, differentiable on `[0,1]` with
`|alpha'| ≤ 4`, whose derivative oscillates by at least `1` on every subinterval meeting `Kset`.
Since `Kset` has measure at least `3/4`, every partition satisfies
`U(P, alpha', id) - L(P, alpha', id) ≥ 3/4`, so `alpha'` is not Riemann integrable, while the
constant integrand `1` is integrable against `alpha`.
-/

/-!
# The Volterra bump on a single interval

For `a < b` set `L = b - a` and

`g a b y = ((y - a) * (b - y) / L) ^ 2 * sin (1 / (y - a))`.

This is the classical Volterra bump, arranged so that it vanishes quadratically at both
endpoints of `[a, b]` while its derivative oscillates with amplitude close to `1` as `y ↓ a`.
-/

namespace VolCalc

open Real

/-- The Volterra bump on the interval `[a, b]`. -/
noncomputable def g (a b y : ℝ) : ℝ :=
  ((y - a) * (b - y) / (b - a)) ^ 2 * Real.sin (1 / (y - a))

/-- The derivative of `VolCalc.g a b` at an interior point. -/
noncomputable def g' (a b y : ℝ) : ℝ :=
  2 * ((y - a) * (b - y)) * (a + b - 2 * y) / (b - a) ^ 2 * Real.sin (1 / (y - a)) -
    (b - y) ^ 2 / (b - a) ^ 2 * Real.cos (1 / (y - a))

theorem hasDerivAt_g {a b y : ℝ} (hay : a < y) (hyb : y < b) :
    HasDerivAt (g a b) (g' a b y) y := by
  have hya : y - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hay)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (by linarith)
  -- the polynomial factor
  have h1 : HasDerivAt (fun t : ℝ => t - a) 1 y := (hasDerivAt_id y).sub_const a
  have h2 : HasDerivAt (fun t : ℝ => b - t) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub b
  have hp : HasDerivAt (fun t : ℝ => (t - a) * (b - t)) (1 * (b - y) + (y - a) * (-1)) y :=
    h1.mul h2
  have hq : HasDerivAt (fun t : ℝ => (t - a) * (b - t) / (b - a))
      ((a + b - 2 * y) / (b - a)) y := (hp.div_const (b - a)).congr_deriv (by ring)
  have hsq : HasDerivAt (fun t : ℝ => ((t - a) * (b - t) / (b - a)) ^ 2)
      (2 * ((y - a) * (b - y) / (b - a)) * ((a + b - 2 * y) / (b - a))) y :=
    (hq.pow 2).congr_deriv (by push_cast; ring)
  -- the oscillating factor
  have hinv : HasDerivAt (fun t : ℝ => 1 / (t - a)) (-1 / (y - a) ^ 2) y := by
    have h : HasDerivAt (fun t : ℝ => (t - a)⁻¹) (-1 / (y - a) ^ 2) y := h1.inv hya
    simpa only [one_div] using h
  have hs : HasDerivAt (fun t : ℝ => Real.sin (1 / (t - a)))
      (Real.cos (1 / (y - a)) * (-1 / (y - a) ^ 2)) y :=
    (Real.hasDerivAt_sin _).comp y hinv
  have hprod : HasDerivAt (fun t : ℝ => ((t - a) * (b - t) / (b - a)) ^ 2 *
      Real.sin (1 / (t - a)))
      (2 * ((y - a) * (b - y) / (b - a)) * ((a + b - 2 * y) / (b - a)) *
          Real.sin (1 / (y - a)) +
        ((y - a) * (b - y) / (b - a)) ^ 2 * (Real.cos (1 / (y - a)) * (-1 / (y - a) ^ 2))) y :=
    hsq.mul hs
  refine hprod.congr_deriv ?_
  set S := Real.sin (1 / (y - a)) with hS
  set C := Real.cos (1 / (y - a)) with hC
  unfold g'
  rw [← hS, ← hC]
  field_simp
  ring

/-- The bump vanishes quadratically at the left endpoint. -/
theorem abs_g_le_left {a b y : ℝ} (hay : a ≤ y) (hyb : y ≤ b) :
    |g a b y| ≤ (y - a) ^ 2 := by
  rcases eq_or_lt_of_le (hay.trans hyb) with hab | hab
  · have hya : y = a := le_antisymm (hab ▸ hyb) hay
    simp [g, hya]
  · have hba : (0:ℝ) < b - a := by linarith
    have hs : |Real.sin (1 / (y - a))| ≤ 1 := Real.abs_sin_le_one _
    have hkey : ((y - a) * (b - y) / (b - a)) ^ 2 ≤ (y - a) ^ 2 := by
      have h1 : (y - a) * (b - y) / (b - a) ≤ y - a := by
        rw [div_le_iff₀ hba]
        nlinarith [sub_nonneg.mpr hay, sub_nonneg.mpr hyb]
      have h2 : 0 ≤ (y - a) * (b - y) / (b - a) := by positivity
      nlinarith
    calc |g a b y| = ((y - a) * (b - y) / (b - a)) ^ 2 * |Real.sin (1 / (y - a))| := by
          rw [g, abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ ((y - a) * (b - y) / (b - a)) ^ 2 * 1 := by
          have : (0:ℝ) ≤ ((y - a) * (b - y) / (b - a)) ^ 2 := by positivity
          nlinarith
      _ ≤ (y - a) ^ 2 := by linarith

/-- The bump vanishes quadratically at the right endpoint. -/
theorem abs_g_le_right {a b y : ℝ} (hay : a ≤ y) (hyb : y ≤ b) :
    |g a b y| ≤ (b - y) ^ 2 := by
  rcases eq_or_lt_of_le (hay.trans hyb) with hab | hab
  · have hya : y = a := le_antisymm (hab ▸ hyb) hay
    simp [g, hya, ← hab]
  · have hba : (0:ℝ) < b - a := by linarith
    have hs : |Real.sin (1 / (y - a))| ≤ 1 := Real.abs_sin_le_one _
    have hkey : ((y - a) * (b - y) / (b - a)) ^ 2 ≤ (b - y) ^ 2 := by
      have h1 : (y - a) * (b - y) / (b - a) ≤ b - y := by
        rw [div_le_iff₀ hba]
        nlinarith [sub_nonneg.mpr hay, sub_nonneg.mpr hyb]
      have h2 : 0 ≤ (y - a) * (b - y) / (b - a) := by positivity
      nlinarith
    calc |g a b y| = ((y - a) * (b - y) / (b - a)) ^ 2 * |Real.sin (1 / (y - a))| := by
          rw [g, abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ ((y - a) * (b - y) / (b - a)) ^ 2 * 1 := by
          have : (0:ℝ) ≤ ((y - a) * (b - y) / (b - a)) ^ 2 := by positivity
          nlinarith
      _ ≤ (b - y) ^ 2 := by linarith

/-- The derivative of the bump is bounded by `3/2` on intervals of length at most `1`. -/
theorem abs_g'_le {a b y : ℝ} (hab : a < b) (hL : b - a ≤ 1) (hay : a ≤ y) (hyb : y ≤ b) :
    |g' a b y| ≤ 3 / 2 := by
  have hba : (0:ℝ) < b - a := by linarith
  have hsq : (0:ℝ) < (b - a) ^ 2 := by positivity
  have hsin : |Real.sin (1 / (y - a))| ≤ 1 := Real.abs_sin_le_one _
  have hcos : |Real.cos (1 / (y - a))| ≤ 1 := Real.abs_cos_le_one _
  have ht1 : |2 * ((y - a) * (b - y)) * (a + b - 2 * y) / (b - a) ^ 2 *
      Real.sin (1 / (y - a))| ≤ 1 / 2 := by
    have hnum : |2 * ((y - a) * (b - y)) * (a + b - 2 * y)| ≤ (b - a) ^ 3 / 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (2 * y - a - b), sq_nonneg (b - y), sq_nonneg (y - a),
        sub_nonneg.mpr hay, sub_nonneg.mpr hyb, sq_nonneg (b - a)]
    have hfrac : |2 * ((y - a) * (b - y)) * (a + b - 2 * y) / (b - a) ^ 2| ≤ (b - a) / 2 := by
      rw [abs_div, abs_of_pos hsq, div_le_iff₀ hsq]
      calc |2 * ((y - a) * (b - y)) * (a + b - 2 * y)| ≤ (b - a) ^ 3 / 2 := hnum
        _ = (b - a) / 2 * (b - a) ^ 2 := by ring
    calc |2 * ((y - a) * (b - y)) * (a + b - 2 * y) / (b - a) ^ 2 * Real.sin (1 / (y - a))|
        = |2 * ((y - a) * (b - y)) * (a + b - 2 * y) / (b - a) ^ 2| *
            |Real.sin (1 / (y - a))| := abs_mul _ _
      _ ≤ (b - a) / 2 * 1 := by
          apply mul_le_mul hfrac hsin (abs_nonneg _) (by positivity)
      _ ≤ 1 / 2 := by linarith
  have ht2 : |(b - y) ^ 2 / (b - a) ^ 2 * Real.cos (1 / (y - a))| ≤ 1 := by
    have hfrac : |(b - y) ^ 2 / (b - a) ^ 2| ≤ 1 := by
      rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hsq, div_le_one hsq]
      nlinarith [sub_nonneg.mpr hay, sub_nonneg.mpr hyb]
    calc |(b - y) ^ 2 / (b - a) ^ 2 * Real.cos (1 / (y - a))|
        = |(b - y) ^ 2 / (b - a) ^ 2| * |Real.cos (1 / (y - a))| := abs_mul _ _
      _ ≤ 1 * 1 := by apply mul_le_mul hfrac hcos (abs_nonneg _) (by positivity)
      _ = 1 := by ring
  calc |g' a b y| ≤ |2 * ((y - a) * (b - y)) * (a + b - 2 * y) / (b - a) ^ 2 *
          Real.sin (1 / (y - a))| + |(b - y) ^ 2 / (b - a) ^ 2 * Real.cos (1 / (y - a))| :=
        abs_sub _ _
    _ ≤ 1 / 2 + 1 := by linarith
    _ ≤ 3 / 2 := by linarith

/-- Arbitrarily close to the left endpoint the derivative of the bump oscillates by at
least `1`. -/
theorem exists_osc {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) :
    ∃ y z, y ∈ Set.Ioo a b ∧ z ∈ Set.Ioo a b ∧ y < a + δ ∧ z < a + δ ∧
      1 ≤ g' a b z - g' a b y := by
  have hba : (0:ℝ) < b - a := by linarith
  set c : ℝ := min δ ((b - a) / 4) with hc
  have hcpos : 0 < c := lt_min hδ (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (2 * π * c))
  set M : ℕ := N + 1 with hM
  have hMpos : (0:ℝ) < (M:ℝ) := by positivity
  have hMgt : 1 / (2 * π * c) < (M:ℝ) := by
    have : (N:ℝ) < (M:ℝ) := by
      rw [hM]; push_cast; linarith
    linarith
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hden : (0:ℝ) < 2 * π * (M:ℝ) := by positivity
  have hy : 1 / (2 * π * (M:ℝ)) < c := by
    rw [div_lt_iff₀ hden]
    have h0 : 0 < 2 * π * c := by positivity
    rw [div_lt_iff₀ h0] at hMgt
    nlinarith
  set y : ℝ := a + 1 / (2 * π * (M:ℝ)) with hydef
  set z : ℝ := a + 1 / ((2 * (M:ℝ) + 1) * π) with hzdef
  have hzden : (0:ℝ) < (2 * (M:ℝ) + 1) * π := by positivity
  have hzlt : 1 / ((2 * (M:ℝ) + 1) * π) < 1 / (2 * π * (M:ℝ)) := by
    apply one_div_lt_one_div_of_lt hden
    nlinarith
  have hyc : y - a < c := by rw [hydef]; simpa using hy
  have hzc : z - a < c := by
    rw [hzdef]; simp only [add_sub_cancel_left]; linarith
  have hcle : c ≤ (b - a) / 4 := min_le_right _ _
  have hcδ : c ≤ δ := min_le_left _ _
  have hya : 0 < y - a := by rw [hydef]; simp; positivity
  have hza : 0 < z - a := by rw [hzdef]; simp; positivity
  have hyb : y < b := by nlinarith
  have hzb : z < b := by nlinarith
  refine ⟨y, z, ⟨by linarith, hyb⟩, ⟨by linarith, hzb⟩, by linarith, by linarith, ?_⟩
  -- evaluate the derivative at the two special points
  have hyval : 1 / (y - a) = (M:ℝ) * (2 * π) := by
    rw [hydef]
    simp only [add_sub_cancel_left, one_div, inv_inv]
    ring
  have hzval : 1 / (z - a) = (M:ℝ) * (2 * π) + π := by
    rw [hzdef]
    simp only [add_sub_cancel_left, one_div, inv_inv]
    ring
  have hsin_y : Real.sin (1 / (y - a)) = 0 := by
    rw [hyval]
    have h : (M:ℝ) * (2 * π) = ((2 * M : ℕ):ℝ) * π := by push_cast; ring
    rw [h]
    exact Real.sin_nat_mul_pi _
  have hcos_y : Real.cos (1 / (y - a)) = 1 := by
    rw [hyval]
    exact Real.cos_nat_mul_two_pi _
  have hsin_z : Real.sin (1 / (z - a)) = 0 := by
    rw [hzval]
    have h : (M:ℝ) * (2 * π) + π = ((2 * M + 1 : ℕ):ℝ) * π := by push_cast; ring
    rw [h]
    exact Real.sin_nat_mul_pi _
  have hcos_z : Real.cos (1 / (z - a)) = -1 := by
    rw [hzval]
    exact Real.cos_nat_mul_two_pi_add_pi _
  have hsq : (0:ℝ) < (b - a) ^ 2 := by positivity
  have hby : 3 * (b - a) / 4 < b - y := by
    have : y - a < (b - a) / 4 := lt_of_lt_of_le hyc hcle
    linarith
  have hbz : 3 * (b - a) / 4 < b - z := by
    have : z - a < (b - a) / 4 := lt_of_lt_of_le hzc hcle
    linarith
  rw [g', g', hsin_y, hcos_y, hsin_z, hcos_z]
  have hgoal : (b - z) ^ 2 / (b - a) ^ 2 + (b - y) ^ 2 / (b - a) ^ 2 ≥ 1 := by
    rw [← add_div, ge_iff_le, le_div_iff₀ hsq]
    nlinarith [hby, hbz, hba]
  linarith [hgoal]

end VolCalc

/-!
# A closed nowhere dense subset of `[0,1]` of positive measure

`Kset` is `[0,1]` with a small open neighbourhood of every rational removed (plus the two
endpoints put back).  It is closed, contains no interval, and has measure at least `3/4`.
-/

namespace VolFat

open Set MeasureTheory
open scoped ENNReal

/-- An enumeration of the rationals. -/
noncomputable def qq (n : ℕ) : ℝ := ((Denumerable.eqv ℚ).symm n : ℚ)

/-- The radius of the interval removed around the `n`-th rational. -/
noncomputable def rad (n : ℕ) : ℝ := 1 / 2 ^ (n + 4)

theorem rad_pos (n : ℕ) : 0 < rad n := by
  unfold rad; positivity

/-- The removed open set: a small interval around each rational. -/
def Uset : Set ℝ := ⋃ n, Ioo (qq n - rad n) (qq n + rad n)

/-- The fat closed nowhere dense set. -/
def Kset : Set ℝ := (Icc 0 1 \ Uset) ∪ {0, 1}

theorem isOpen_Uset : IsOpen Uset :=
  isOpen_iUnion fun _ => isOpen_Ioo

theorem isClosed_Kset : IsClosed Kset := by
  have h1 : IsClosed (Icc (0:ℝ) 1 \ Uset) := isClosed_Icc.sdiff isOpen_Uset
  have h2 : IsClosed ({0, 1} : Set ℝ) := (Set.toFinite ({0, 1} : Set ℝ)).isClosed
  exact h1.union h2

theorem Kset_subset : Kset ⊆ Icc (0:ℝ) 1 := by
  rintro x (⟨hx, -⟩ | hx)
  · exact hx
  · rcases hx with rfl | rfl <;> norm_num

theorem zero_mem_Kset : (0:ℝ) ∈ Kset := by
  simp [Kset]

theorem one_mem_Kset : (1:ℝ) ∈ Kset := by
  simp [Kset]

theorem rat_mem_Uset (q : ℚ) : (q:ℝ) ∈ Uset := by
  refine Set.mem_iUnion.mpr ⟨Denumerable.eqv ℚ q, ?_⟩
  have hq : qq (Denumerable.eqv ℚ q) = (q:ℝ) := by
    simp [qq]
  rw [hq]
  exact ⟨by linarith [rad_pos (Denumerable.eqv ℚ q)], by linarith [rad_pos (Denumerable.eqv ℚ q)]⟩

/-- Every nondegenerate subinterval of `[0,1]` contains a point outside `Kset`. -/
theorem exists_not_mem_Kset {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    ∃ y ∈ Ioo u v, y ∉ Kset := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn huv
  refine ⟨(q:ℝ), ⟨hq1, hq2⟩, ?_⟩
  have hU : (q:ℝ) ∈ Uset := rat_mem_Uset q
  have h0 : (0:ℝ) < q := lt_of_le_of_lt hu hq1
  have h1 : (q:ℝ) < 1 := lt_of_lt_of_le hq2 hv
  rintro (⟨-, hnot⟩ | hmem)
  · exact hnot hU
  · rcases hmem with h | h
    · exact absurd h (ne_of_gt h0)
    · exact absurd h (ne_of_lt h1)

theorem volume_Uset_le : volume Uset ≤ ENNReal.ofReal (1 / 4) := by
  have hstep : ∀ n : ℕ, volume (Ioo (qq n - rad n) (qq n + rad n)) ≤
      ENNReal.ofReal ((1/2 : ℝ) ^ (n + 3)) := by
    intro n
    rw [Real.volume_Ioo]
    have hlen : qq n + rad n - (qq n - rad n) = 2 * rad n := by ring
    have h2 : 2 * rad n = (1/2 : ℝ) ^ (n + 3) := by
      have h : (2:ℝ) ^ (n + 4) = 2 ^ (n + 3) * 2 := by rw [pow_succ]
      unfold rad
      rw [div_pow, one_pow, h]
      field_simp
    rw [hlen, h2]
  have hnonneg : ∀ n : ℕ, (0:ℝ) ≤ (1/2 : ℝ) ^ (n + 3) := fun n => by positivity
  have hpow : ∀ n : ℕ, (1/2 : ℝ) ^ (n + 3) = (1/2 : ℝ) ^ 3 * (1/2 : ℝ) ^ n := by
    intro n; rw [pow_add]; ring
  have hsummable : Summable (fun n : ℕ => (1/2 : ℝ) ^ (n + 3)) := by
    refine Summable.congr ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).mul_left ((1/2 : ℝ) ^ 3)) ?_
    intro n
    exact (hpow n).symm
  have hsum : ∑' n : ℕ, (1/2 : ℝ) ^ (n + 3) = 1 / 4 := by
    rw [tsum_congr hpow, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)]
    norm_num
  calc volume Uset ≤ ∑' n : ℕ, volume (Ioo (qq n - rad n) (qq n + rad n)) :=
        measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((1/2 : ℝ) ^ (n + 3)) := ENNReal.tsum_le_tsum hstep
    _ = ENNReal.ofReal (∑' n : ℕ, (1/2 : ℝ) ^ (n + 3)) :=
        (ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable).symm
    _ = ENNReal.ofReal (1 / 4) := by rw [hsum]

/-- The set `Kset` has measure at least `3/4`. -/
theorem volume_Kset_ge : ENNReal.ofReal (3 / 4) ≤ volume Kset := by
  have hsub : (Icc (0:ℝ) 1 \ Uset) ⊆ Kset := Set.subset_union_left
  have hdiff : volume (Icc (0:ℝ) 1) - volume Uset ≤ volume (Icc (0:ℝ) 1 \ Uset) :=
    le_measure_sdiff
  have hIcc : volume (Icc (0:ℝ) 1) = 1 := by simp
  have hone : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 4) = ENNReal.ofReal (3 / 4) := by
    refine ENNReal.sub_eq_of_eq_add (by simp) ?_
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  calc ENNReal.ofReal (3 / 4) = (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 4) := hone.symm
    _ ≤ (1 : ℝ≥0∞) - volume Uset := tsub_le_tsub_left volume_Uset_le 1
    _ = volume (Icc (0:ℝ) 1) - volume Uset := by rw [hIcc]
    _ ≤ volume (Icc (0:ℝ) 1 \ Uset) := hdiff
    _ ≤ volume Kset := measure_mono hsub

end VolFat

/-!
# A Volterra integrator: Theorem 6.17 needs the integrability of `α'`

We assemble the Volterra bumps of `VolCalc` on the complementary intervals of the fat closed
nowhere dense set `VolFat.Kset` and add `2x`.  The resulting `alpha` is strictly increasing and
differentiable on `[0,1]` with bounded derivative, but the derivative oscillates by at least `1`
on every subinterval meeting `Kset`, hence is not Riemann integrable.
-/

namespace VolMain

open Set MeasureTheory Rudin VolFat VolCalc
open scoped ENNReal

/-- The last point of `Kset` at or before `x`. -/
noncomputable def A (x : ℝ) : ℝ := sSup (Kset ∩ Iic x)

/-- The first point of `Kset` at or after `x`. -/
noncomputable def B (x : ℝ) : ℝ := sInf (Kset ∩ Ici x)

/-- The Volterra function: the bump of `VolCalc` on each complementary interval of `Kset`. -/
noncomputable def V (x : ℝ) : ℝ := if 0 < x ∧ x < 1 then g (A x) (B x) x else 0

open Classical in
/-- The derivative of `VolMain.V`. -/
noncomputable def Vd (x : ℝ) : ℝ := if x ∈ Kset then 0 else g' (A x) (B x) x

/-- The Volterra integrator. -/
noncomputable def alpha (x : ℝ) : ℝ := 2 * x + V x

/-! ### The endpoints of the complementary interval -/

theorem Kle_nonempty {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : (Kset ∩ Iic x).Nonempty :=
  ⟨0, zero_mem_Kset, hx.1⟩

theorem Kle_bddAbove (x : ℝ) : BddAbove (Kset ∩ Iic x) := ⟨x, fun _ hy => hy.2⟩

theorem Kge_nonempty {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : (Kset ∩ Ici x).Nonempty :=
  ⟨1, one_mem_Kset, hx.2⟩

theorem Kge_bddBelow (x : ℝ) : BddBelow (Kset ∩ Ici x) := ⟨x, fun _ hy => hy.2⟩

theorem A_mem {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : A x ∈ Kset :=
  ((isClosed_Kset.inter isClosed_Iic).csSup_mem (Kle_nonempty hx) (Kle_bddAbove x)).1

theorem A_le {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : A x ≤ x :=
  csSup_le (Kle_nonempty hx) fun _ hy => hy.2

theorem le_A {x z : ℝ} (hz : z ∈ Kset) (hzx : z ≤ x) : z ≤ A x :=
  le_csSup (Kle_bddAbove x) ⟨hz, hzx⟩

theorem B_mem {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : B x ∈ Kset :=
  ((isClosed_Kset.inter isClosed_Ici).csInf_mem (Kge_nonempty hx) (Kge_bddBelow x)).1

theorem le_B {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : x ≤ B x :=
  le_csInf (Kge_nonempty hx) fun _ hy => hy.2

theorem B_le {x z : ℝ} (hz : z ∈ Kset) (hxz : x ≤ z) : B x ≤ z :=
  csInf_le (Kge_bddBelow x) ⟨hz, hxz⟩

theorem A_nonneg {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : 0 ≤ A x := (Kset_subset (A_mem hx)).1

theorem B_le_one {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : B x ≤ 1 := (Kset_subset (B_mem hx)).2

theorem mem_Ioo_of_not_mem_K {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hxK : x ∉ Kset) :
    0 < x ∧ x < 1 := by
  constructor
  · rcases lt_or_eq_of_le hx.1 with h | h
    · exact h
    · exact absurd (h ▸ zero_mem_Kset) hxK
  · rcases lt_or_eq_of_le hx.2 with h | h
    · exact h
    · exact absurd (h ▸ one_mem_Kset) hxK

theorem A_lt {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hxK : x ∉ Kset) : A x < x := by
  rcases lt_or_eq_of_le (A_le hx) with h | h
  · exact h
  · exact absurd (h ▸ A_mem hx) hxK

theorem lt_B {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hxK : x ∉ Kset) : x < B x := by
  rcases lt_or_eq_of_le (le_B hx) with h | h
  · exact h
  · exact absurd (by rw [h]; exact B_mem hx) hxK

/-- The open interval between the two neighbouring points of `Kset` misses `Kset`. -/
theorem not_mem_K_of_mem_Ioo {x y : ℝ} (hy : y ∈ Ioo (A x) (B x)) : y ∉ Kset := by
  intro hyK
  rcases le_total y x with h | h
  · exact absurd (le_A hyK h) (not_le.mpr hy.1)
  · exact absurd (B_le hyK h) (not_le.mpr hy.2)

theorem mem_Icc_of_mem_Ioo {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Ioo (A x) (B x)) :
    y ∈ Icc (0:ℝ) 1 :=
  ⟨le_of_lt (lt_of_le_of_lt (A_nonneg hx) hy.1), le_of_lt (lt_of_lt_of_le hy.2 (B_le_one hx))⟩

theorem A_eq_of_mem_Ioo {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Ioo (A x) (B x)) :
    A y = A x := by
  have hyIcc : y ∈ Icc (0:ℝ) 1 := mem_Icc_of_mem_Ioo hx hy
  refine le_antisymm ?_ (le_A (A_mem hx) hy.1.le)
  by_contra hcon
  have hcon' : A x < A y := not_le.mp hcon
  have h1 : A y ∈ Ioo (A x) (B x) :=
    ⟨hcon', lt_of_le_of_lt (A_le hyIcc) hy.2⟩
  exact not_mem_K_of_mem_Ioo h1 (A_mem hyIcc)

theorem B_eq_of_mem_Ioo {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Ioo (A x) (B x)) :
    B y = B x := by
  have hyIcc : y ∈ Icc (0:ℝ) 1 := mem_Icc_of_mem_Ioo hx hy
  refine le_antisymm (B_le (B_mem hx) hy.2.le) ?_
  by_contra hcon
  have hcon' : B y < B x := not_le.mp hcon
  have h1 : B y ∈ Ioo (A x) (B x) :=
    ⟨lt_of_lt_of_le hy.1 (le_B hyIcc), hcon'⟩
  exact not_mem_K_of_mem_Ioo h1 (B_mem hyIcc)

/-! ### The Volterra function -/

theorem A_eq_self_of_mem_K {x : ℝ} (hx : x ∈ Kset) : A x = x :=
  le_antisymm (A_le (Kset_subset hx)) (le_A hx le_rfl)

theorem V_eq_zero_of_mem_K {x : ℝ} (hx : x ∈ Kset) : V x = 0 := by
  unfold V
  split_ifs with h
  · rw [A_eq_self_of_mem_K hx]
    simp [g]
  · rfl

theorem V_eq_of_mem_Ioo {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Ioo (A x) (B x)) :
    V y = g (A x) (B x) y := by
  have hyIcc : y ∈ Icc (0:ℝ) 1 := mem_Icc_of_mem_Ioo hx hy
  have hyK : y ∉ Kset := not_mem_K_of_mem_Ioo hy
  have hy01 := mem_Ioo_of_not_mem_K hyIcc hyK
  unfold V
  rw [if_pos hy01, A_eq_of_mem_Ioo hx hy, B_eq_of_mem_Ioo hx hy]

/-- `V` vanishes to second order at every point of `Kset`. -/
theorem abs_V_le {x : ℝ} (hx : x ∈ Kset) (y : ℝ) : |V y| ≤ (y - x) ^ 2 := by
  unfold V
  split_ifs with hy01
  · have hyIcc : y ∈ Icc (0:ℝ) 1 := ⟨hy01.1.le, hy01.2.le⟩
    have hay : A y ≤ y := A_le hyIcc
    have hyb : y ≤ B y := le_B hyIcc
    rcases le_total x y with h | h
    · have hxA : x ≤ A y := le_A hx h
      calc |g (A y) (B y) y| ≤ (y - A y) ^ 2 := abs_g_le_left hay hyb
        _ ≤ (y - x) ^ 2 := by
            have h1 : 0 ≤ y - A y := by linarith
            have h2 : y - A y ≤ y - x := by linarith
            nlinarith
    · have hBx : B y ≤ x := B_le hx h
      calc |g (A y) (B y) y| ≤ (B y - y) ^ 2 := abs_g_le_right hay hyb
        _ ≤ (y - x) ^ 2 := by
            have h1 : 0 ≤ B y - y := by linarith
            have h2 : B y - y ≤ x - y := by linarith
            nlinarith
  · simp
    positivity

theorem hasDerivAt_V_of_mem_K {x : ℝ} (hx : x ∈ Kset) : HasDerivAt V 0 x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hV0 : V x = 0 := V_eq_zero_of_mem_K hx
  have hbound : ∀ y : ℝ, ‖slope V x y‖ ≤ |y - x| := by
    intro y
    rcases eq_or_ne y x with rfl | hne
    · simp
    · have hxy : y - x ≠ 0 := sub_ne_zero.mpr hne
      rw [slope_def_field, hV0, Real.norm_eq_abs, abs_div,
        div_le_iff₀ (abs_pos.mpr hxy)]
      have h1 : |V y - 0| ≤ (y - x) ^ 2 := by simpa using abs_V_le hx y
      calc |V y - 0| ≤ (y - x) ^ 2 := h1
        _ = |y - x| * |y - x| := by rw [← sq_abs]; ring
  have htend : Filter.Tendsto (fun y : ℝ => |y - x|) (nhdsWithin x {x}ᶜ) (nhds 0) := by
    have : Filter.Tendsto (fun y : ℝ => |y - x|) (nhds x) (nhds 0) := by
      have hc : Continuous (fun y : ℝ => |y - x|) := (continuous_id.sub continuous_const).abs
      have := hc.tendsto x
      simpa using this
    exact this.mono_left nhdsWithin_le_nhds
  exact squeeze_zero_norm hbound htend

theorem hasDerivAt_V_of_not_mem_K {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hxK : x ∉ Kset) :
    HasDerivAt V (g' (A x) (B x) x) x := by
  have hax : A x < x := A_lt hx hxK
  have hxb : x < B x := lt_B hx hxK
  have hg : HasDerivAt (g (A x) (B x)) (g' (A x) (B x) x) x := hasDerivAt_g hax hxb
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hax hxb] with y hy
  exact V_eq_of_mem_Ioo hx hy

theorem hasDerivAt_V {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : HasDerivAt V (Vd x) x := by
  classical
  by_cases h : x ∈ Kset
  · simpa [Vd, h] using hasDerivAt_V_of_mem_K h
  · simpa [Vd, h] using hasDerivAt_V_of_not_mem_K hx h

theorem hasDerivAt_alpha {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : HasDerivAt alpha (2 + Vd x) x := by
  have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2:ℝ)
  have h2 := h1.add (hasDerivAt_V hx)
  exact h2

theorem deriv_alpha {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : deriv alpha x = 2 + Vd x :=
  (hasDerivAt_alpha hx).deriv

theorem abs_Vd_le {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : |Vd x| ≤ 3 / 2 := by
  classical
  by_cases h : x ∈ Kset
  · simp [Vd, h]
    norm_num
  · have hax : A x < x := A_lt hx h
    have hxb : x < B x := lt_B hx h
    have hL : B x - A x ≤ 1 := by
      have h1 : 0 ≤ A x := A_nonneg hx
      have h2 : B x ≤ 1 := B_le_one hx
      linarith
    simp only [Vd, if_neg h]
    exact abs_g'_le (lt_trans hax hxb) hL hax.le hxb.le

theorem deriv_alpha_pos {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : 0 < deriv alpha x := by
  have := abs_le.mp (abs_Vd_le hx)
  rw [deriv_alpha hx]; linarith [this.1]

theorem abs_deriv_alpha_le {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : |deriv alpha x| ≤ 4 := by
  have := abs_le.mp (abs_Vd_le hx)
  rw [deriv_alpha hx, abs_le]
  constructor <;> linarith [this.1, this.2]

theorem continuousOn_alpha : ContinuousOn alpha (Icc (0:ℝ) 1) := fun _ hx =>
  ((hasDerivAt_alpha hx).continuousAt).continuousWithinAt

theorem monotoneOn_alpha : MonotoneOn alpha (Icc (0:ℝ) 1) := by
  refine (strictMonoOn_of_deriv_pos (convex_Icc 0 1) continuousOn_alpha ?_).monotoneOn
  intro x hx
  rw [interior_Icc] at hx
  exact deriv_alpha_pos ⟨hx.1.le, hx.2.le⟩

/-! ### The derivative is not Riemann integrable -/

theorem bddAbove_image {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 1) :
    BddAbove (deriv alpha '' Icc u v) := by
  refine ⟨4, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hyIcc : y ∈ Icc (0:ℝ) 1 := ⟨le_trans hu hy.1, le_trans hy.2 hv⟩
  exact (abs_le.mp (abs_deriv_alpha_le hyIcc)).2

theorem bddBelow_image {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 1) :
    BddBelow (deriv alpha '' Icc u v) := by
  refine ⟨-4, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hyIcc : y ∈ Icc (0:ℝ) 1 := ⟨le_trans hu hy.1, le_trans hy.2 hv⟩
  exact (abs_le.mp (abs_deriv_alpha_le hyIcc)).1

/-- On every subinterval meeting `Kset` in its interior the derivative oscillates by at
least `1`. -/
theorem osc_ge {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 1) (hK : (Kset ∩ Ioo u v).Nonempty) :
    1 ≤ sSup (deriv alpha '' Icc u v) - sInf (deriv alpha '' Icc u v) := by
  obtain ⟨c, hcK, hcu, hcv⟩ := hK
  have hc0 : 0 ≤ c := (Kset_subset hcK).1
  obtain ⟨y0, hy0mem, hy0K⟩ := exists_not_mem_Kset hc0 hcv hv
  have hy0Icc : y0 ∈ Icc (0:ℝ) 1 := ⟨le_trans hc0 hy0mem.1.le, le_trans hy0mem.2.le hv⟩
  set a := A y0 with ha
  set b := B y0 with hb
  have hay0 : a < y0 := A_lt hy0Icc hy0K
  have hy0b : y0 < b := lt_B hy0Icc hy0K
  have hca : c ≤ a := le_A hcK hy0mem.1.le
  have hab : a < b := lt_trans hay0 hy0b
  obtain ⟨p, q, hp, hq, hpδ, hqδ, hosc⟩ :=
    exists_osc (a := a) (b := b) (δ := y0 - a) hab (by linarith)
  -- both points lie in `Ioo u v`
  have hpuv : p ∈ Icc u v := by
    constructor
    · have : u < c := hcu
      linarith [hp.1]
    · have : p < y0 := by linarith [hpδ]
      linarith [hy0mem.2]
  have hquv : q ∈ Icc u v := by
    constructor
    · have : u < c := hcu
      linarith [hq.1]
    · have : q < y0 := by linarith [hqδ]
      linarith [hy0mem.2]
  -- the derivative at these points is given by the bump
  have hderiv : ∀ w : ℝ, w ∈ Ioo a b → deriv alpha w = 2 + g' a b w := by
    intro w hw
    have hwIcc : w ∈ Icc (0:ℝ) 1 := mem_Icc_of_mem_Ioo hy0Icc hw
    have hwK : w ∉ Kset := not_mem_K_of_mem_Ioo hw
    rw [deriv_alpha hwIcc]
    classical
    rw [show Vd w = g' (A w) (B w) w by simp [Vd, hwK]]
    rw [A_eq_of_mem_Ioo hy0Icc hw, B_eq_of_mem_Ioo hy0Icc hw]
  have hdp : deriv alpha p = 2 + g' a b p := hderiv p hp
  have hdq : deriv alpha q = 2 + g' a b q := hderiv q hq
  have hsup : deriv alpha q ≤ sSup (deriv alpha '' Icc u v) :=
    le_csSup (bddAbove_image hu hv) ⟨q, hquv, rfl⟩
  have hinf : sInf (deriv alpha '' Icc u v) ≤ deriv alpha p :=
    csInf_le (bddBelow_image hu hv) ⟨p, hpuv, rfl⟩
  linarith [hosc, hdp, hdq, hsup, hinf]

/-! ### Partitions -/

/-- Division points of a partition increase with the index. -/
theorem x_mono {a b : ℝ} (P : Partition a b) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ P.n → P.x i ≤ P.x j := by
  intro i j hij hjn
  induction j with
  | zero =>
      have : i = 0 := Nat.le_zero.mp hij
      simp [this]
  | succ k ih =>
      have hk : k < P.n := hjn
      rcases Nat.eq_or_lt_of_le hij with h | h
      · exact le_of_eq (by rw [h])
      · have hik : i ≤ k := Nat.lt_succ_iff.mp h
        exact (ih hik (le_of_lt hk)).trans (P.mono k hk)

/-- Every division point lies in the interval. -/
theorem x_mem {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.x i ∈ Icc a b := by
  constructor
  · have h := x_mono P (Nat.zero_le i) hi
    rwa [P.first] at h
  · have h := x_mono P hi (le_refl P.n)
    rwa [P.last] at h

/-- Every point of `[0,1]` is a left endpoint of the partition or lies in one of its
subintervals. -/
theorem exists_subinterval (P : Partition (0:ℝ) 1) {c : ℝ} (hc : c ∈ Icc (0:ℝ) 1) :
    c = P.x 0 ∨ ∃ i < P.n, c ∈ Icc (P.x i) (P.x (i + 1)) := by
  have key : ∀ m : ℕ, m ≤ P.n → c ≤ P.x m →
      (c ≤ P.x 0 ∨ ∃ i < m, c ∈ Icc (P.x i) (P.x (i + 1))) := by
    intro m
    induction m with
    | zero => intro _ h; exact Or.inl h
    | succ k ih =>
        intro hk hle
        by_cases hck : c ≤ P.x k
        · rcases ih (Nat.le_of_succ_le hk) hck with h | ⟨i, hi, hmem⟩
          · exact Or.inl h
          · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hmem⟩
        · exact Or.inr ⟨k, Nat.lt_succ_self k, ⟨le_of_not_ge hck, hle⟩⟩
  have hcn : c ≤ P.x P.n := by rw [P.last]; exact hc.2
  rcases key P.n le_rfl hcn with h | ⟨i, hi, hmem⟩
  · have h0 : P.x 0 ≤ c := by rw [P.first]; exact hc.1
    exact Or.inl (le_antisymm h h0)
  · exact Or.inr ⟨i, hi, hmem⟩

open Classical in
/-- The subintervals of a partition that meet `Kset` in their interior cover `Kset` up to a
finite set, so their total length is at least `3/4`. -/
theorem cover_bound (P : Partition (0:ℝ) 1) :
    3 / 4 ≤ ∑ i ∈ (Finset.range P.n).filter
        (fun i => (Kset ∩ Ioo (P.x i) (P.x (i + 1))).Nonempty), (P.x (i + 1) - P.x i) := by
  classical
  set S := (Finset.range P.n).filter
    (fun i => (Kset ∩ Ioo (P.x i) (P.x (i + 1))).Nonempty) with hSdef
  set F : Finset ℝ := (Finset.range (P.n + 1)).image P.x with hFdef
  have hcover : Kset ⊆ (⋃ i ∈ S, Ioo (P.x i) (P.x (i + 1))) ∪ (F : Set ℝ) := by
    intro c hc
    have hcIcc : c ∈ Icc (0:ℝ) 1 := Kset_subset hc
    rcases exists_subinterval P hcIcc with h | ⟨i, hi, hmem⟩
    · refine Or.inr ?_
      simp only [hFdef, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
      exact ⟨0, by omega, h.symm⟩
    · rcases lt_or_eq_of_le hmem.1 with h1 | h1
      · rcases lt_or_eq_of_le hmem.2 with h2 | h2
        · refine Or.inl ?_
          have hiS : i ∈ S := by
            simp only [hSdef, Finset.mem_filter, Finset.mem_range]
            exact ⟨hi, ⟨c, hc, h1, h2⟩⟩
          exact Set.mem_biUnion hiS ⟨h1, h2⟩
        · refine Or.inr ?_
          simp only [hFdef, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
          exact ⟨i + 1, by omega, h2.symm⟩
      · refine Or.inr ?_
        simp only [hFdef, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
        exact ⟨i, by omega, h1⟩
  have hFzero : volume (F : Set ℝ) = 0 := (F.finite_toSet).measure_zero volume
  have hmeas : volume Kset ≤ ∑ i ∈ S, ENNReal.ofReal (P.x (i + 1) - P.x i) := by
    calc volume Kset ≤ volume ((⋃ i ∈ S, Ioo (P.x i) (P.x (i + 1))) ∪ (F : Set ℝ)) :=
          measure_mono hcover
      _ ≤ volume (⋃ i ∈ S, Ioo (P.x i) (P.x (i + 1))) + volume (F : Set ℝ) :=
          measure_union_le _ _
      _ = volume (⋃ i ∈ S, Ioo (P.x i) (P.x (i + 1))) := by rw [hFzero, add_zero]
      _ ≤ ∑ i ∈ S, volume (Ioo (P.x i) (P.x (i + 1))) := measure_biUnion_finset_le _ _
      _ = ∑ i ∈ S, ENNReal.ofReal (P.x (i + 1) - P.x i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Real.volume_Ioo]
  have hnn : ∀ i ∈ S, 0 ≤ P.x (i + 1) - P.x i := by
    intro i hi
    have hi' : i < P.n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    exact sub_nonneg.mpr (P.mono i hi')
  have hkey : ENNReal.ofReal (3 / 4) ≤ ENNReal.ofReal (∑ i ∈ S, (P.x (i + 1) - P.x i)) := by
    rw [ENNReal.ofReal_sum_of_nonneg hnn]
    exact le_trans volume_Kset_ge hmeas
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg hnn)).mp hkey

open Classical in
theorem sum_bound (P : Partition (0:ℝ) 1) :
    3 / 4 ≤ upperSum (deriv alpha) id P - lowerSum (deriv alpha) id P := by
  classical
  set S := (Finset.range P.n).filter
    (fun i => (Kset ∩ Ioo (P.x i) (P.x (i + 1))).Nonempty) with hSdef
  have hIcc : ∀ i, i < P.n → Icc (P.x i) (P.x (i + 1)) ⊆ Icc (0:ℝ) 1 := by
    intro i hi
    exact Set.Icc_subset_Icc (x_mem P (le_of_lt hi)).1 (x_mem P (Nat.succ_le_of_lt hi)).2
  have hdiff : upperSum (deriv alpha) id P - lowerSum (deriv alpha) id P
      = ∑ i ∈ Finset.range P.n, (sSup (deriv alpha '' Icc (P.x i) (P.x (i + 1))) -
          sInf (deriv alpha '' Icc (P.x i) (P.x (i + 1)))) * (P.x (i + 1) - P.x i) := by
    rw [upperSum, lowerSum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [id_eq]
    ring
  rw [hdiff]
  have hterm_nonneg : ∀ i ∈ Finset.range P.n,
      0 ≤ (sSup (deriv alpha '' Icc (P.x i) (P.x (i + 1))) -
        sInf (deriv alpha '' Icc (P.x i) (P.x (i + 1)))) * (P.x (i + 1) - P.x i) := by
    intro i hi
    have hi' : i < P.n := Finset.mem_range.mp hi
    have hle : P.x i ≤ P.x (i + 1) := P.mono i hi'
    have hmi : P.x i ∈ Icc (0:ℝ) 1 := x_mem P (le_of_lt hi')
    have hmi1 : P.x (i + 1) ∈ Icc (0:ℝ) 1 := x_mem P (Nat.succ_le_of_lt hi')
    have hne : (deriv alpha '' Icc (P.x i) (P.x (i + 1))).Nonempty :=
      ⟨deriv alpha (P.x i), P.x i, ⟨le_rfl, hle⟩, rfl⟩
    have h0 : sInf (deriv alpha '' Icc (P.x i) (P.x (i + 1))) ≤
        sSup (deriv alpha '' Icc (P.x i) (P.x (i + 1))) :=
      csInf_le_csSup hne (bddBelow_image hmi.1 hmi1.2) (bddAbove_image hmi.1 hmi1.2)
    have := sub_nonneg.mpr hle
    exact mul_nonneg (by linarith) this
  have hSsub : S ⊆ Finset.range P.n := Finset.filter_subset _ _
  calc (3:ℝ) / 4 ≤ ∑ i ∈ S, (P.x (i + 1) - P.x i) := cover_bound P
    _ ≤ ∑ i ∈ S, (sSup (deriv alpha '' Icc (P.x i) (P.x (i + 1))) -
          sInf (deriv alpha '' Icc (P.x i) (P.x (i + 1)))) * (P.x (i + 1) - P.x i) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi' : i < P.n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
        have hK : (Kset ∩ Ioo (P.x i) (P.x (i + 1))).Nonempty :=
          (Finset.mem_filter.mp hi).2
        have hle : P.x i ≤ P.x (i + 1) := P.mono i hi'
        have hmi : P.x i ∈ Icc (0:ℝ) 1 := x_mem P (le_of_lt hi')
        have hmi1 : P.x (i + 1) ∈ Icc (0:ℝ) 1 := x_mem P (Nat.succ_le_of_lt hi')
        have hosc := osc_ge hmi.1 hmi1.2 hK
        nlinarith [sub_nonneg.mpr hle]
    _ ≤ ∑ i ∈ Finset.range P.n, (sSup (deriv alpha '' Icc (P.x i) (P.x (i + 1))) -
          sInf (deriv alpha '' Icc (P.x i) (P.x (i + 1)))) * (P.x (i + 1) - P.x i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun i hi _ => hterm_nonneg i hi)

theorem not_riemannIntegrable : ¬ RiemannIntegrable 0 1 (deriv alpha) := by
  intro h
  have hmono : MonotoneOn (id : ℝ → ℝ) (Icc (0:ℝ) 1) := fun _ _ _ _ hab => hab
  have hb : ∃ M, ∀ x ∈ Icc (0:ℝ) 1, |deriv alpha x| ≤ M :=
    ⟨4, fun _ hx => abs_deriv_alpha_le hx⟩
  have hcrit := (Rudin.ch06_riemann_criterion 0 1 (by norm_num) (deriv alpha) id hmono hb).mp h
  obtain ⟨P, hP⟩ := hcrit (3 / 4) (by norm_num)
  linarith [sum_bound P]

end VolMain

/-!
# Theorem 6.17 needs the Riemann integrability of the density

The Volterra integrator of `VolMain` refutes Rudin's Theorem 6.17 once the hypothesis
`α' ∈ ℛ` is dropped, even though every boundedness hypothesis of Chapter 6 holds.
-/

namespace VolFinalAux

open Rudin

/-- Division points of a partition increase with the index. -/
theorem x_mono {a b : ℝ} (P : Partition a b) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ P.n → P.x i ≤ P.x j := by
  intro i j hij hjn
  induction j with
  | zero =>
      have : i = 0 := Nat.le_zero.mp hij
      simp [this]
  | succ k ih =>
      have hk : k < P.n := hjn
      rcases Nat.eq_or_lt_of_le hij with h | h
      · exact le_of_eq (by rw [h])
      · have hik : i ≤ k := Nat.lt_succ_iff.mp h
        exact (ih hik (le_of_lt hk)).trans (P.mono k hk)

/-- Every division point lies in the interval. -/
theorem x_mem {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  constructor
  · have h := x_mono P (Nat.zero_le i) hi
    rwa [P.first] at h
  · have h := x_mono P hi (le_refl P.n)
    rwa [P.last] at h

/-- The trivial partition of `[0, 1]` with a single subinterval. -/
def trivPart : Partition (0:ℝ) 1 where
  n := 1
  x := fun i => if i = 0 then 0 else 1
  first := by simp
  last := by norm_num
  mono := by
    intro i hi
    interval_cases i
    norm_num

/-- The upper sum of the constant integrand `1` telescopes. -/
theorem upperSum_one (β : ℝ → ℝ) (P : Partition (0:ℝ) 1) :
    upperSum (fun _ => (1:ℝ)) β P = β 1 - β 0 := by
  have hterm : ∀ i ∈ Finset.range P.n,
      sSup ((fun _ => (1:ℝ)) '' Set.Icc (P.x i) (P.x (i + 1))) * (β (P.x (i + 1)) - β (P.x i))
        = β (P.x (i + 1)) - β (P.x i) := by
    intro i hi
    have hle : P.x i ≤ P.x (i + 1) := P.mono i (Finset.mem_range.mp hi)
    have himg : ((fun _ => (1:ℝ)) '' Set.Icc (P.x i) (P.x (i + 1))) = {1} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨P.x i, ⟨le_rfl, hle⟩, rfl⟩, ?_⟩
      rintro _ ⟨x, _, rfl⟩
      rfl
    rw [himg, csSup_singleton, one_mul]
  rw [upperSum, Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun i => β (P.x i)),
    P.first, P.last]

/-- The lower sum of the constant integrand `1` telescopes. -/
theorem lowerSum_one (β : ℝ → ℝ) (P : Partition (0:ℝ) 1) :
    lowerSum (fun _ => (1:ℝ)) β P = β 1 - β 0 := by
  have hterm : ∀ i ∈ Finset.range P.n,
      sInf ((fun _ => (1:ℝ)) '' Set.Icc (P.x i) (P.x (i + 1))) * (β (P.x (i + 1)) - β (P.x i))
        = β (P.x (i + 1)) - β (P.x i) := by
    intro i hi
    have hle : P.x i ≤ P.x (i + 1) := P.mono i (Finset.mem_range.mp hi)
    have himg : ((fun _ => (1:ℝ)) '' Set.Icc (P.x i) (P.x (i + 1))) = {1} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨P.x i, ⟨le_rfl, hle⟩, rfl⟩, ?_⟩
      rintro _ ⟨x, _, rfl⟩
      rfl
    rw [himg, csInf_singleton, one_mul]
  rw [lowerSum, Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun i => β (P.x i)),
    P.first, P.last]

/-- The constant integrand `1` is integrable against any integrator. -/
theorem rsIntegrable_one (β : ℝ → ℝ) : RSIntegrable 0 1 (fun _ => (1:ℝ)) β := by
  have hup : upperIntegral 0 1 (fun _ => (1:ℝ)) β = β 1 - β 0 := by
    have hset : {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = upperSum (fun _ => (1:ℝ)) β P}
        = {β 1 - β 0} := by
      ext y
      constructor
      · rintro ⟨P, rfl⟩
        simp [upperSum_one β P]
      · rintro rfl
        exact ⟨trivPart, (upperSum_one β trivPart).symm⟩
    unfold upperIntegral
    rw [hset, csInf_singleton]
  have hlo : lowerIntegral 0 1 (fun _ => (1:ℝ)) β = β 1 - β 0 := by
    have hset : {y : ℝ | ∃ P : Partition (0:ℝ) 1, y = lowerSum (fun _ => (1:ℝ)) β P}
        = {β 1 - β 0} := by
      ext y
      constructor
      · rintro ⟨P, rfl⟩
        simp [lowerSum_one β P]
      · rintro rfl
        exact ⟨trivPart, (lowerSum_one β trivPart).symm⟩
    unfold lowerIntegral
    rw [hset, csSup_singleton]
  unfold RSIntegrable
  rw [hup, hlo]

end VolFinalAux

open Rudin VolFinalAux

/-- Rudin's Theorem 6.17 fails if the Riemann integrability of `α'` is dropped, even with all
the boundedness hypotheses of Chapter 6 in force: there is a monotonically increasing `α`,
differentiable at every point of `[0,1]` with bounded derivative, such that `α' ∉ ℛ` while the
bounded integrand `f = 1` satisfies `f ∈ ℛ(α)`. -/
theorem solution :
    ∃ α : ℝ → ℝ,
      MonotoneOn α (Set.Icc 0 1) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt α (deriv α x) x) ∧
      (∃ K, ∀ x ∈ Set.Icc (0:ℝ) 1, |deriv α x| ≤ K) ∧
      ¬ RiemannIntegrable 0 1 (deriv α) ∧
      RSIntegrable 0 1 (fun _ => (1:ℝ)) α ∧
      ¬ RiemannIntegrable 0 1 (fun x => (1:ℝ) * deriv α x) := by
  refine ⟨VolMain.alpha, VolMain.monotoneOn_alpha, ?_, ⟨4, fun x hx => VolMain.abs_deriv_alpha_le hx⟩,
    VolMain.not_riemannIntegrable, rsIntegrable_one _, ?_⟩
  · intro x hx
    rw [VolMain.deriv_alpha hx]
    exact VolMain.hasDerivAt_alpha hx
  · have hfun : (fun x => (1:ℝ) * deriv VolMain.alpha x) = deriv VolMain.alpha := by
      funext x; rw [one_mul]
    rw [hfun]
    exact VolMain.not_riemannIntegrable
