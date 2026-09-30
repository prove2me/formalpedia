-- Prove2me | solution 1 for SP4Mission.compl_singleton_simplyConnected
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-09T02:29:31.083558+00:00
-- url     : https://prove2.me/submissions/22914b72-301f-406f-8c30-93070217ae63

import Definitions.Def_SP4Sphere

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open SP4Mission

/-!
# Removing a point from a simply connected `n`-manifold, `n ≥ 3`

Let `M` be a Hausdorff topological space with an atlas modelled on `ℝⁿ`, `n ≥ 3`, which is simply
connected, and let `p ∈ M`. Then `M ∖ {p}` is simply connected.

The textbook argument (van Kampen for `M = (M ∖ {p}) ∪ B`, `B` a coordinate ball) is not available
in Mathlib, so we give a direct *general position* proof: every map `H : I × I → M` can be pushed
off `p` by a modification supported in a small coordinate ball and fixed on any prescribed closed
set `F ⊆ I × I` whose image misses `p`.

**Push-off lemma** (`PushOff.pushoff`). Fix a chart `e` at `p` with `c := e p` and a ball
`ball c R ⊆ e.target` so small that `e.symm (closedBall c R)` misses `H '' F` (possible since
`H '' F` is compact and misses `p`). Put `K := H⁻¹(e.symm '' closedBall c (R/4))`, a compact set
disjoint from `F` and contained in the open set `U₀ := H⁻¹(e.symm '' ball c (R/2))`. Choose
`δ > 0` with `cthickening (3δ) K ⊆ U₀`, and on the compact set `C₃ := cthickening (3δ) K`
consider `g := e ∘ H`, uniformly continuous. For a fine grid `1/m < δ` (and `1/m` below the
modulus of continuity at `ε := R/16`), let `Q` be the bilinear interpolant of the grid values of
`g` (with value `0` at grid points outside `C₃`); `Q` is Lipschitz and `‖Q - g‖ ≤ ε` on
`R₂ := cthickening (2δ) K`. A Lipschitz image of `ℝ²` has Hausdorff dimension `≤ 2 < n`, so there
is a translation vector `w` with `‖w‖ < ε` and `c - w ∉ range Q`; thus `Q + w` never hits `c`.
Finally interpolate: with the cutoff `λ(z) := clamp₀¹(2 - infDist z K / δ)`, which is `1` on `K`
and `0` on `∂R₂`, set `y := (1 - λ) g + λ (Q + w)` and `H' := e.symm ∘ y` on `R₂`, `H' := H`
outside. On `R₂`, `‖y - g‖ ≤ 2ε` keeps `y` inside `ball c R`; where `λ = 1` we have
`y = Q + w ≠ c`, and where `λ < 1` the point lies outside `K`, so `‖g - c‖ > R/4 > 2ε` and again
`y ≠ c`. Hence `H'` misses `p`, is continuous (the two definitions agree on `∂R₂`), and agrees
with `H` on `F` (as `F ∩ R₂ = ∅`).

**Assembly.** `M ∖ {p}` is nonempty (`n ≥ 1`), path connected (push a path of `M` between two
points of `M ∖ {p}`, viewed as a map on `I × I` constant in the second variable, off `p` keeping
the end points), and every loop `γ` in `M ∖ {p}` is null-homotopic: a null-homotopy of `γ` in `M`
is fixed on `∂(I × I)`, whose image misses `p`; pushing it off `p` gives a null-homotopy in
`M ∖ {p}`.
-/


open Set Metric unitInterval

namespace PushOff

/-! ### 1. Hat functions on `ℝ`, bilinear weights on `ℝ × ℝ` -/

/-- Hat function of the grid `{k / m}` on `ℝ`. -/
noncomputable def hat (m k : ℕ) (s : ℝ) : ℝ := max 0 (1 - |s * m - k|)

theorem hat_nonneg (m k : ℕ) (s : ℝ) : 0 ≤ hat m k s := le_max_left _ _

theorem hat_le_one (m k : ℕ) (s : ℝ) : hat m k s ≤ 1 := by
  unfold hat
  apply max_le zero_le_one
  linarith [abs_nonneg (s * m - k)]

theorem hat_pos_iff (m k : ℕ) (s : ℝ) : 0 < hat m k s ↔ |s * m - k| < 1 := by
  unfold hat
  rw [lt_max_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (lt_irrefl 0)
    · linarith
  · intro h
    right
    linarith

theorem hat_eq_zero_of_one_le (m k : ℕ) (s : ℝ) (h : 1 ≤ |s * m - k|) : hat m k s = 0 :=
  max_eq_left (by linarith)

theorem continuous_hat (m k : ℕ) : Continuous (hat m k) := by
  unfold hat
  fun_prop

/-- Hat functions are `m`-Lipschitz. -/
theorem hat_lipschitz (m k : ℕ) : LipschitzWith m (hat m k) := by
  apply LipschitzWith.of_dist_le_mul
  intro s s'
  unfold hat
  rw [Real.dist_eq, Real.dist_eq]
  set A := abs (s * m - k) with hA
  set B := abs (s' * m - k) with hB
  have h1 : abs (max 0 (1 - A) - max 0 (1 - B)) ≤ abs ((1 - A) - (1 - B)) :=
    (abs_max_sub_max_le_max _ _ _ _).trans (by simp)
  have h2 : abs ((1 - A) - (1 - B)) = abs (B - A) := by
    congr 1; ring
  have h3 : abs (B - A) ≤ abs ((s' * m - k) - (s * m - k)) := abs_abs_sub_abs_le_abs_sub _ _
  have h4 : abs ((s' * m - k) - (s * m - k)) = (m : ℝ) * abs (s - s') := by
    rw [show (s' * m - k) - (s * m - k) = (m : ℝ) * (s' - s) by ring, abs_mul, Nat.abs_cast,
      abs_sub_comm]
  calc abs (max 0 (1 - A) - max 0 (1 - B))
      ≤ abs ((1 - A) - (1 - B)) := h1
    _ = abs (B - A) := h2
    _ ≤ abs ((s' * m - k) - (s * m - k)) := h3
    _ = (m : ℝ) * abs (s - s') := h4
    _ = ((m : NNReal) : ℝ) * abs (s - s') := by simp

/-- Support of the hat: if `hat m k s ≠ 0` then `|s - k/m| < 1/m`. -/
theorem dist_of_hat_ne_zero {m k : ℕ} (hm : 0 < m) {s : ℝ} (h : hat m k s ≠ 0) :
    |s - k / m| < 1 / m := by
  have hpos : 0 < hat m k s := lt_of_le_of_ne (hat_nonneg m k s) (Ne.symm h)
  rw [hat_pos_iff] at hpos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have : s - k / m = (s * m - k) / m := by field_simp
  rw [this, abs_div, abs_of_pos hm', div_lt_div_iff_of_pos_right hm']
  exact hpos

/-- Only the two hats adjacent to `s` are nonzero: `k ∈ {a, a+1}` with `a = min ⌊s m⌋₊ (m-1)`. -/
theorem hat_index {m : ℕ} (hm : 0 < m) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {k : ℕ}
    (hk : k ≤ m) (h : hat m k s ≠ 0) :
    k = min ⌊s * m⌋₊ (m - 1) ∨ k = min ⌊s * m⌋₊ (m - 1) + 1 := by
  have hpos : 0 < hat m k s := lt_of_le_of_ne (hat_nonneg m k s) (Ne.symm h)
  rw [hat_pos_iff, abs_sub_lt_iff] at hpos
  obtain ⟨h1, h2⟩ := hpos
  have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hu0 : (0 : ℝ) ≤ s * m := mul_nonneg hs0 hm'
  have hfl : (⌊s * m⌋₊ : ℝ) ≤ s * m := Nat.floor_le hu0
  have hfu : s * m < ⌊s * m⌋₊ + 1 := Nat.lt_floor_add_one _
  have hum : s * m ≤ m := by nlinarith
  have hfk : ⌊s * m⌋₊ ≤ k := by
    have : (⌊s * m⌋₊ : ℝ) < k + 1 := by linarith
    have : ⌊s * m⌋₊ < k + 1 := by exact_mod_cast this
    omega
  have hkf : k ≤ ⌊s * m⌋₊ + 1 := by
    have : (k : ℝ) < ⌊s * m⌋₊ + 2 := by linarith
    have : k < ⌊s * m⌋₊ + 2 := by exact_mod_cast this
    omega
  have hfm : ⌊s * m⌋₊ ≤ m := by
    have : (⌊s * m⌋₊ : ℝ) ≤ m := hfl.trans hum
    exact_mod_cast this
  omega

/-- Partition of unity: the hats sum to `1` on `[0, 1]`. -/
theorem sum_hat {m : ℕ} (hm : 0 < m) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑ k ∈ Finset.range (m + 1), hat m k s = 1 := by
  set a := min ⌊s * m⌋₊ (m - 1) with ha
  have ham : a + 1 ≤ m := by omega
  have hsub : ({a, a + 1} : Finset ℕ) ⊆ Finset.range (m + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_pair (by omega)]
    -- explicit values: `hat m a s = 1 - α`, `hat m (a+1) s = α` with `α = s m - a ∈ [0, 1]`
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hu0 : (0 : ℝ) ≤ s * m := mul_nonneg hs0 hm'
    have hum : s * m ≤ m := by nlinarith
    have hα0 : (a : ℝ) ≤ s * m := by
      have h1 : (⌊s * m⌋₊ : ℝ) ≤ s * m := Nat.floor_le hu0
      have h2 : (a : ℝ) ≤ ⌊s * m⌋₊ := by exact_mod_cast (min_le_left _ _)
      linarith
    have hα1 : s * m ≤ a + 1 := by
      rcases le_or_gt ⌊s * m⌋₊ (m - 1) with h | h
      · have : a = ⌊s * m⌋₊ := min_eq_left h
        rw [this]
        exact (Nat.lt_floor_add_one _).le
      · have : a = m - 1 := min_eq_right h.le
        rw [this]
        have : ((m - 1 : ℕ) : ℝ) + 1 = m := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        rw [this]
        exact hum
    unfold hat
    have e1 : |s * m - a| = s * m - a := abs_of_nonneg (by linarith)
    have e2 : |s * m - ((a + 1 : ℕ) : ℝ)| = a + 1 - s * m := by
      push_cast
      rw [abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [e1, e2, max_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  · intro k hk hk'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
    rw [Finset.mem_range] at hk
    by_contra hne
    rcases hat_index hm hs0 hs1 (by omega) hne with h | h
    · exact hk'.1 h
    · exact hk'.2 h


/-! ### 2. Bilinear weights and the interpolant on `ℝ × ℝ` -/

section Interp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bilinear weight of the grid vertex `(i / m, j / m)`. -/
noncomputable def wt (m i j : ℕ) (z : ℝ × ℝ) : ℝ := hat m i z.1 * hat m j z.2

theorem wt_nonneg (m i j : ℕ) (z : ℝ × ℝ) : 0 ≤ wt m i j z :=
  mul_nonneg (hat_nonneg _ _ _) (hat_nonneg _ _ _)

theorem continuous_wt (m i j : ℕ) : Continuous (wt m i j) :=
  ((continuous_hat m i).comp continuous_fst).mul ((continuous_hat m j).comp continuous_snd)

/-- The bilinear weights are `2m`-Lipschitz for the sup metric on `ℝ × ℝ`. -/
theorem wt_lipschitz (m i j : ℕ) : LipschitzWith (2 * m) (wt m i j) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  unfold wt
  have h1 : dist (hat m i z.1) (hat m i z'.1) ≤ m * dist z z' := by
    have := (hat_lipschitz m i).dist_le_mul z.1 z'.1
    have h2 : dist z.1 z'.1 ≤ dist z z' := by rw [Prod.dist_eq]; exact le_max_left _ _
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    calc dist (hat m i z.1) (hat m i z'.1) ≤ ((m : NNReal) : ℝ) * dist z.1 z'.1 := this
      _ = (m : ℝ) * dist z.1 z'.1 := by simp
      _ ≤ (m : ℝ) * dist z z' := by gcongr
  have h2 : dist (hat m j z.2) (hat m j z'.2) ≤ m * dist z z' := by
    have := (hat_lipschitz m j).dist_le_mul z.2 z'.2
    have h2 : dist z.2 z'.2 ≤ dist z z' := by rw [Prod.dist_eq]; exact le_max_right _ _
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    calc dist (hat m j z.2) (hat m j z'.2) ≤ ((m : NNReal) : ℝ) * dist z.2 z'.2 := this
      _ = (m : ℝ) * dist z.2 z'.2 := by simp
      _ ≤ (m : ℝ) * dist z z' := by gcongr
  rw [Real.dist_eq] at h1 h2 ⊢
  have ha := hat_nonneg m i z'.1
  have ha1 := hat_le_one m i z'.1
  have hb := hat_nonneg m j z.2
  have hb1 := hat_le_one m j z.2
  have key : hat m i z.1 * hat m j z.2 - hat m i z'.1 * hat m j z'.2
      = (hat m i z.1 - hat m i z'.1) * hat m j z.2 + hat m i z'.1 * (hat m j z.2 - hat m j z'.2) := by
    ring
  rw [key]
  calc |(hat m i z.1 - hat m i z'.1) * hat m j z.2 + hat m i z'.1 * (hat m j z.2 - hat m j z'.2)|
      ≤ |(hat m i z.1 - hat m i z'.1) * hat m j z.2| + |hat m i z'.1 * (hat m j z.2 - hat m j z'.2)| :=
        abs_add_le _ _
    _ = |hat m i z.1 - hat m i z'.1| * hat m j z.2 + hat m i z'.1 * |hat m j z.2 - hat m j z'.2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg ha]
    _ ≤ (m * dist z z') * 1 + 1 * (m * dist z z') := by
        gcongr
    _ = ((2 * m : NNReal) : ℝ) * dist z z' := by push_cast; ring

theorem sum_wt {m : ℕ} (hm : 0 < m) {z : ℝ × ℝ} (h1 : z.1 ∈ Set.Icc (0 : ℝ) 1)
    (h2 : z.2 ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), wt m i j z = 1 := by
  unfold wt
  rw [← Finset.sum_mul_sum, sum_hat hm h1.1 h1.2, sum_hat hm h2.1 h2.2, one_mul]

theorem wt_ne_zero {m i j : ℕ} (hm : 0 < m) {z : ℝ × ℝ} (h : wt m i j z ≠ 0) :
    |z.1 - i / m| < 1 / m ∧ |z.2 - j / m| < 1 / m := by
  unfold wt at h
  exact ⟨dist_of_hat_ne_zero hm (left_ne_zero_of_mul h),
    dist_of_hat_ne_zero hm (right_ne_zero_of_mul h)⟩

/-- Bilinear interpolant of grid values `v i j` placed at the vertices `(i / m, j / m)`. -/
noncomputable def interp (m : ℕ) (v : ℕ → ℕ → E) (z : ℝ × ℝ) : E :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), wt m i j z • v i j

theorem continuous_interp (m : ℕ) (v : ℕ → ℕ → E) : Continuous (interp m v) := by
  unfold interp
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_wt m i j).smul continuous_const

/-- The interpolant is Lipschitz. -/
theorem interp_lipschitz (m : ℕ) (v : ℕ → ℕ → E) : ∃ K : NNReal, LipschitzWith K (interp m v) := by
  set S : ℝ := ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), ‖v i j‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  refine ⟨⟨2 * m * S, by positivity⟩, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  unfold interp
  have hterm : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (m + 1),
      dist (wt m i j z • v i j) (wt m i j z' • v i j) ≤ (2 * m * dist z z') * ‖v i j‖ := by
    intro i _ j _
    rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, ← Real.dist_eq]
    gcongr
    have := (wt_lipschitz m i j).dist_le_mul z z'
    simpa using this
  calc dist (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), wt m i j z • v i j)
        (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), wt m i j z' • v i j)
      ≤ ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), (2 * m * dist z z') * ‖v i j‖ := by
        apply dist_sum_sum_le_of_le
        intro i hi
        exact dist_sum_sum_le_of_le _ (hterm i hi)
    _ = (2 * m * dist z z') * S := by
        rw [hS, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = ((⟨2 * m * S, by positivity⟩ : NNReal) : ℝ) * dist z z' := by
        simp only
        ring

/-- Approximation: if every grid value with nonzero weight at `z` is within `ε` of `x`, so is
the interpolant. -/
theorem norm_interp_sub_le {m : ℕ} (hm : 0 < m) (v : ℕ → ℕ → E) {z : ℝ × ℝ}
    (h1 : z.1 ∈ Set.Icc (0 : ℝ) 1) (h2 : z.2 ∈ Set.Icc (0 : ℝ) 1) (x : E) {ε : ℝ}
    (hv : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (m + 1), wt m i j z ≠ 0 →
      ‖v i j - x‖ ≤ ε) :
    ‖interp m v z - x‖ ≤ ε := by
  have hx : x = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), wt m i j z • x := by
    simp_rw [← Finset.sum_smul, sum_wt hm h1 h2, one_smul]
  have hε : 0 ≤ ε := by
    -- there is a nonzero weight (weights sum to 1), so `ε ≥ ‖_‖ ≥ 0`
    by_contra hneg
    rw [not_le] at hneg
    have hsum := sum_wt hm h1 h2
    have hall : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (m + 1), wt m i j z = 0 := by
      intro i hi j hj
      by_contra hne
      exact absurd (hv i hi j hj hne) (not_le.mpr (lt_of_lt_of_le hneg (norm_nonneg _)))
    rw [Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (hall i hi))] at hsum
    exact zero_ne_one hsum
  calc ‖interp m v z - x‖
      = ‖∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), wt m i j z • (v i j - x)‖ := by
        unfold interp
        conv_lhs => rw [hx]
        rw [← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_sub]
    _ ≤ ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), ‖wt m i j z • (v i j - x)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), wt m i j z * ε := by
        gcongr with i hi j hj
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (wt_nonneg m i j z)]
        rcases eq_or_ne (wt m i j z) 0 with h0 | h0
        · rw [h0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hv i hi j hj h0) (wt_nonneg m i j z)
    _ = ε := by
        simp_rw [← Finset.sum_mul, sum_wt hm h1 h2, one_mul]

end Interp


/-! ### 3. General position: a Lipschitz image of the plane misses a point of every ball, `n ≥ 3` -/

theorem exists_avoid {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hn : 3 ≤ Module.finrank ℝ E) {P : ℝ × ℝ → E} {K : NNReal} (hP : LipschitzWith K P)
    (c : E) {ε : ℝ} (hε : 0 < ε) : ∃ w : E, ‖w‖ < ε ∧ c - w ∉ Set.range P := by
  by_contra h
  rw [not_exists] at h
  have hsub : Metric.ball (0 : E) ε ⊆ (fun x : E => c - x) '' Set.range P := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    have hw' : c - w ∈ Set.range P := by
      by_contra hc
      exact h w ⟨hw, hc⟩
    exact ⟨c - w, hw', by simp⟩
  have h1 : dimH (Metric.ball (0 : E) ε) = Module.finrank ℝ E :=
    Real.dimH_of_mem_nhds (Metric.ball_mem_nhds 0 hε)
  have hlip : LipschitzWith 1 (fun x : E => c - x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_sub_left]
    simp
  have h2 : dimH ((fun x : E => c - x) '' Set.range P) ≤ 2 := by
    calc dimH ((fun x : E => c - x) '' Set.range P) ≤ dimH (Set.range P) := hlip.dimH_image_le _
      _ = dimH (P '' Set.univ) := by rw [Set.image_univ]
      _ ≤ dimH (Set.univ : Set (ℝ × ℝ)) := hP.dimH_image_le _
      _ = Module.finrank ℝ (ℝ × ℝ) := Real.dimH_univ_eq_finrank _
      _ = 2 := by
        rw [Module.finrank_prod, Module.finrank_self]
        norm_num
  have h3 := (dimH_mono hsub).trans h2
  rw [h1] at h3
  have h4 : ((3 : ℕ) : ENNReal) ≤ (Module.finrank ℝ E : ENNReal) := by exact_mod_cast hn
  have h5 : ((3 : ℕ) : ENNReal) ≤ 2 := h4.trans h3
  norm_num at h5


/-! ### 4. The push-off lemma -/

/-- Membership in a closed thickening of a nonempty set, via `infDist`. -/
theorem mem_cthick_iff {X : Type*} [PseudoMetricSpace X] {K : Set X} (hK : K.Nonempty) {δ : ℝ}
    (hδ : 0 ≤ δ) (x : X) : x ∈ cthickening δ K ↔ infDist x K ≤ δ := by
  rw [mem_cthickening_iff, infDist, ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hK) hδ]

/-- Grid point `k / m` of the unit interval (clamped). -/
noncomputable def gpI (m k : ℕ) : I := Set.projIcc 0 1 zero_le_one ((k : ℝ) / m)

theorem gpI_coe {m k : ℕ} (hm : 0 < m) (hk : k ≤ m) : ((gpI m k : I) : ℝ) = k / m := by
  unfold gpI
  rw [Set.projIcc_of_mem]
  constructor
  · positivity
  · rw [div_le_one (by exact_mod_cast hm)]
    exact_mod_cast hk

variable {n : ℕ}

/-- **Push-off lemma.** A map `H : I × I → M` into an `n`-manifold (`n ≥ 3`) can be modified,
keeping it fixed on a closed set `F` whose image misses `p`, so that it misses `p` everywhere. -/
theorem pushoff (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hn : 3 ≤ n) (p : M)
    (H : C(I × I, M)) (F : Set (I × I)) (hF : IsClosed F) (hHF : ∀ z ∈ F, H z ≠ p) :
    ∃ H' : C(I × I, M), (∀ z, H' z ≠ p) ∧ ∀ z ∈ F, H' z = H z := by
  classical
  set e := chartAt (EuclideanSpace ℝ (Fin n)) p with he
  have hp : p ∈ e.source := mem_chart_source _ p
  set c : EuclideanSpace ℝ (Fin n) := e p with hc
  -- Step 1: a closed coordinate ball around `p` inside the chart, missing `H '' F`.
  obtain ⟨R₀, hR₀, hball⟩ := Metric.isOpen_iff.mp e.open_target c (e.map_source hp)
  have hA : IsCompact (H '' F) := hF.isCompact.image H.continuous
  have hpA : p ∉ H '' F := by
    rintro ⟨z, hz, hzp⟩
    exact hHF z hz hzp
  have hAc : (H '' F)ᶜ ∈ nhds p := hA.isClosed.isOpen_compl.mem_nhds hpA
  have hmap : (H '' F)ᶜ ∈ Filter.map e.symm (nhds c) := by
    rw [hc, e.symm_map_nhds_eq hp]
    exact hAc
  rw [Filter.mem_map] at hmap
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hmap
  set R : ℝ := min R₀ ρ / 2 with hR
  have hRpos : 0 < R := by positivity
  have hRR₀ : R < R₀ := by
    have : min R₀ ρ ≤ R₀ := min_le_left _ _
    linarith
  have hRρ : R < ρ := by
    have : min R₀ ρ ≤ ρ := min_le_right _ _
    linarith
  have hcb : closedBall c R ⊆ e.target := fun y hy =>
    hball (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) hRR₀))
  have hSA : ∀ y ∈ closedBall c R, e.symm y ∉ H '' F := fun y hy =>
    hρsub (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) hRρ))
  -- Step 2: the compact set `K` where `H` is close to `p`, and the open set `U₀`.
  set S : Set M := e.symm '' closedBall c (R / 4) with hS
  have hSc : IsCompact S :=
    (isCompact_closedBall c (R / 4)).image_of_continuousOn
      (e.continuousOn_symm.mono ((closedBall_subset_closedBall (by linarith)).trans hcb))
  have hpS : p ∈ S := ⟨c, mem_closedBall_self (by linarith), by rw [hc, e.left_inv hp]⟩
  set K : Set (I × I) := H ⁻¹' S with hK
  have hKc : IsClosed K := hSc.isClosed.preimage H.continuous
  have hKcpt : IsCompact K := hKc.isCompact
  set U₀ : Set (I × I) := H ⁻¹' (e.source ∩ e ⁻¹' ball c (R / 2)) with hU₀
  have hU₀o : IsOpen U₀ := (e.isOpen_inter_preimage isOpen_ball).preimage H.continuous
  have hKU₀ : K ⊆ U₀ := by
    rintro z ⟨y, hy, hyz⟩
    have hyt : y ∈ e.target := hcb (closedBall_subset_closedBall (by linarith) hy)
    refine ⟨?_, ?_⟩
    · show H z ∈ e.source
      rw [← hyz]
      exact e.map_target hyt
    · show e (H z) ∈ ball c (R / 2)
      rw [← hyz, e.right_inv hyt]
      exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) (by linarith))
  have hU₀F : ∀ z ∈ F, z ∉ U₀ := by
    intro z hz ⟨h1, h2⟩
    apply hSA (e (H z)) (mem_closedBall.mpr (le_of_lt (lt_trans (mem_ball.mp h2) (by linarith))))
    rw [e.left_inv h1]
    exact ⟨z, hz, rfl⟩
  -- Points outside `K` are not sent to `p`.
  have hnotK : ∀ z, z ∉ K → H z ≠ p := fun z hz hzp => hz (by rw [hK, Set.mem_preimage, hzp]; exact hpS)
  -- Trivial case: `K = ∅`.
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨H, fun z => hnotK z (by rw [hKe]; exact Set.notMem_empty z), fun z _ => rfl⟩
  -- Step 3: thickenings.
  obtain ⟨δ₀, hδ₀, hC₃⟩ := hKcpt.exists_cthickening_subset_open hU₀o hKU₀
  set δ : ℝ := δ₀ / 3 with hδdef
  have hδ : 0 < δ := by positivity
  set C₃ : Set (I × I) := cthickening δ₀ K with hC₃def
  set R₂ : Set (I × I) := cthickening (2 * δ) K with hR₂def
  have hR₂C₃ : R₂ ⊆ C₃ := cthickening_mono (by linarith) K
  have hR₂U₀ : R₂ ⊆ U₀ := hR₂C₃.trans hC₃
  have hKR₂ : K ⊆ R₂ := self_subset_cthickening K
  have hR₂closed : IsClosed R₂ := isClosed_cthickening
  have hC₃cpt : IsCompact C₃ := isClosed_cthickening.isCompact
  -- the chart image of `H`
  set g : I × I → EuclideanSpace ℝ (Fin n) := fun z => e (H z) with hg
  have hgU₀ : ∀ z ∈ U₀, H z ∈ e.source ∧ g z ∈ ball c (R / 2) := fun z hz => hz
  have hgcont : ContinuousOn g (H ⁻¹' e.source) :=
    e.continuousOn.comp H.continuous.continuousOn (fun z hz => hz)
  have hU₀src : U₀ ⊆ H ⁻¹' e.source := fun z hz => (hgU₀ z hz).1
  -- Step 4: uniform continuity of `g` on `C₃`.
  set ε : ℝ := R / 16 with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuousOn_iff.mp
    (hC₃cpt.uniformContinuousOn_of_continuous (hgcont.mono (hC₃.trans hU₀src))) ε hεpos
  -- Step 5: the mesh.
  obtain ⟨m₀, hm₀⟩ := exists_nat_one_div_lt (lt_min hδ hη)
  set m : ℕ := m₀ + 1 with hm_def
  have hm : 0 < m := Nat.succ_pos m₀
  have hmδ : 1 / (m : ℝ) < δ := by
    rw [hm_def]; push_cast; exact lt_of_lt_of_le hm₀ (min_le_left _ _)
  have hmη : 1 / (m : ℝ) < η := by
    rw [hm_def]; push_cast; exact lt_of_lt_of_le hm₀ (min_le_right _ _)
  -- grid values and the interpolant
  set v : ℕ → ℕ → EuclideanSpace ℝ (Fin n) := fun i j =>
    if ((gpI m i, gpI m j) : I × I) ∈ C₃ then g (gpI m i, gpI m j) else 0 with hv
  set P : ℝ × ℝ → EuclideanSpace ℝ (Fin n) := interp m v with hP
  set Q : I × I → EuclideanSpace ℝ (Fin n) := fun z => P ((z.1 : ℝ), (z.2 : ℝ)) with hQ
  have hQcont : Continuous Q :=
    (continuous_interp m v).comp (continuous_subtype_val.prodMap continuous_subtype_val)
  -- Step 6: approximation on `R₂`.
  have happrox : ∀ z ∈ R₂, ‖Q z - g z‖ ≤ ε := by
    intro z hz
    have hz2 : infDist z K ≤ 2 * δ := (mem_cthick_iff hKne (by linarith) z).mp hz
    apply norm_interp_sub_le hm v z.1.2 z.2.2 (g z)
    intro i hi j hj hw
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi hj
    obtain ⟨h1, h2⟩ := wt_ne_zero hm hw
    set G : I × I := (gpI m i, gpI m j) with hG
    have hdist : dist G z < 1 / m := by
      rw [Prod.dist_eq, max_lt_iff, Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq,
        gpI_coe hm hi, gpI_coe hm hj]
      exact ⟨by rw [abs_sub_comm]; exact h1, by rw [abs_sub_comm]; exact h2⟩
    have hGC₃ : G ∈ C₃ := by
      rw [mem_cthick_iff hKne hδ₀.le]
      calc infDist G K ≤ infDist z K + dist G z := infDist_le_infDist_add_dist
        _ ≤ 2 * δ + 1 / m := by gcongr
        _ ≤ δ₀ := by linarith
    have hvG : v i j = g G := by
      simp only [hv]
      rw [if_pos hGC₃]
    rw [hvG]
    have := hηg G hGC₃ z (hR₂C₃ hz) (lt_trans hdist hmη)
    rw [dist_eq_norm] at this
    exact this.le
  -- Step 7: the generic translation `w`.
  have hfin : 3 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [finrank_euclideanSpace_fin]; exact hn
  obtain ⟨Kl, hKl⟩ := interp_lipschitz m v
  obtain ⟨w, hw, hwP⟩ := exists_avoid hfin hKl c hεpos
  -- Step 8: the cutoff and the modified map.
  set lam : I × I → ℝ := fun z => max 0 (min 1 (2 - infDist z K / δ)) with hlam
  have hlamc : Continuous lam := by
    apply Continuous.max continuous_const
    apply Continuous.min continuous_const
    exact continuous_const.sub (Continuous.div_const (continuous_infDist_pt (s := K)) δ)
  have hlam0 : ∀ z, 0 ≤ lam z := fun z => le_max_left _ _
  have hlam1 : ∀ z, lam z ≤ 1 := fun z => max_le zero_le_one (min_le_left _ _)
  set y : I × I → EuclideanSpace ℝ (Fin n) := fun z => (1 - lam z) • g z + lam z • (Q z + w) with hy
  set f : I × I → M := fun z => e.symm (y z) with hf
  -- estimates on `R₂`
  have hy_close : ∀ z ∈ R₂, ‖y z - g z‖ ≤ 2 * ε := by
    intro z hz
    have : y z - g z = lam z • (Q z + w - g z) := by
      simp only [hy]
      rw [smul_sub, sub_smul, one_smul, smul_add]
      abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hlam0 z)]
    calc lam z * ‖Q z + w - g z‖ ≤ 1 * ‖Q z + w - g z‖ :=
          mul_le_mul_of_nonneg_right (hlam1 z) (norm_nonneg _)
      _ = ‖(Q z - g z) + w‖ := by rw [one_mul]; congr 1; abel
      _ ≤ ‖Q z - g z‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ε + ε := add_le_add (happrox z hz) hw.le
      _ = 2 * ε := by ring
  have hy_in : ∀ z ∈ R₂, y z ∈ ball c R := by
    intro z hz
    have hgz : g z ∈ ball c (R / 2) := (hgU₀ z (hR₂U₀ hz)).2
    rw [mem_ball, dist_eq_norm] at hgz ⊢
    calc ‖y z - c‖ = ‖(y z - g z) + (g z - c)‖ := by congr 1; abel
      _ ≤ ‖y z - g z‖ + ‖g z - c‖ := norm_add_le _ _
      _ < 2 * ε + R / 2 := add_lt_add_of_le_of_lt (hy_close z hz) hgz
      _ ≤ R := by rw [hε]; linarith
  have hy_ne : ∀ z ∈ R₂, y z ≠ c := by
    intro z hz hyc
    rcases eq_or_lt_of_le (hlam1 z) with h1 | h1
    · -- `lam z = 1`: `y z = Q z + w`
      have hyz : y z = Q z + w := by
        simp only [hy]
        rw [h1, sub_self, zero_smul, zero_add, one_smul]
      apply hwP
      refine ⟨((z.1 : ℝ), (z.2 : ℝ)), ?_⟩
      show P (z.1, z.2) = c - w
      have : Q z = P ((z.1 : ℝ), (z.2 : ℝ)) := rfl
      rw [← this, ← hyc, hyz]
      abel
    · -- `lam z < 1`: `z ∉ K`, so `g z` is far from `c`
      have hzK : z ∉ K := by
        intro hzK
        have h0 : infDist z K = 0 := infDist_zero_of_mem hzK
        have : lam z = 1 := by
          simp only [hlam]
          rw [h0, zero_div, sub_zero, min_eq_left (by norm_num), max_eq_right (by norm_num)]
        exact absurd this (ne_of_lt h1)
      have hHz : H z ∈ e.source := (hgU₀ z (hR₂U₀ hz)).1
      have hfar : R / 4 < ‖g z - c‖ := by
        by_contra hle
        rw [not_lt] at hle
        apply hzK
        show H z ∈ S
        refine ⟨g z, ?_, ?_⟩
        · rw [mem_closedBall, dist_eq_norm]; exact hle
        · exact e.left_inv hHz
      have := hy_close z hz
      rw [hyc, norm_sub_rev, hε] at this
      linarith
  have hf_ne : ∀ z ∈ R₂, f z ≠ p := by
    intro z hz hfz
    apply hy_ne z hz
    have hyt : y z ∈ e.target := hcb (ball_subset_closedBall (hy_in z hz))
    calc y z = e (e.symm (y z)) := (e.right_inv hyt).symm
      _ = e p := by rw [← hfz]
      _ = c := rfl
  -- Step 9: assemble.
  have hfcont : ContinuousOn f R₂ := by
    have hycont : ContinuousOn y R₂ := by
      apply ContinuousOn.add
      · exact (continuous_const.sub hlamc).continuousOn.smul (hgcont.mono (hR₂U₀.trans hU₀src))
      · exact hlamc.continuousOn.smul (hQcont.add continuous_const).continuousOn
    exact e.continuousOn_symm.comp hycont (fun z hz => hcb (ball_subset_closedBall (hy_in z hz)))
  have hfront : ∀ z ∈ frontier R₂, f z = H z := by
    intro z hz
    have hzR₂ : z ∈ R₂ := hR₂closed.frontier_subset hz
    have hinf : infDist z K = 2 * δ := by
      have := frontier_cthickening_subset K hz
      simp only [Set.mem_ofPred_eq] at this
      rw [infDist, this, ENNReal.toReal_ofReal (by linarith)]
    have hlz : lam z = 0 := by
      simp only [hlam]
      rw [hinf, mul_div_assoc, div_self hδ.ne', mul_one, sub_self, min_eq_right zero_le_one, max_self]
    have hyz : y z = g z := by
      simp only [hy]
      rw [hlz, sub_zero, one_smul, zero_smul, add_zero]
    show e.symm (y z) = H z
    rw [hyz]
    exact e.left_inv (hgU₀ z (hR₂U₀ hzR₂)).1
  refine ⟨⟨R₂.piecewise f H, ?_⟩, ?_, ?_⟩
  · apply continuous_piecewise hfront
    · rw [hR₂closed.closure_eq]; exact hfcont
    · exact H.continuous.continuousOn
  · intro z
    show R₂.piecewise f H z ≠ p
    by_cases hz : z ∈ R₂
    · rw [Set.piecewise_eq_of_mem _ _ _ hz]; exact hf_ne z hz
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz]
      exact hnotK z (fun hzK => hz (hKR₂ hzK))
  · intro z hz
    show R₂.piecewise f H z = H z
    rw [Set.piecewise_eq_of_notMem _ _ _ (fun h => hU₀F z hz (hR₂U₀ h))]

/-! ### 5. Assembly: the punctured manifold is simply connected -/

section Assembly

open scoped Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

omit [T2Space M] in
/-- The complement of a point in a charted space modelled on `ℝⁿ`, `n ≥ 1`, is nonempty. -/
theorem nonempty_compl_singleton (hn : 1 ≤ n) (p : M) : Nonempty {x : M // x ≠ p} := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  set e := chartAt (EuclideanSpace ℝ (Fin n)) p with he
  have ht : ∀ᶠ q in 𝓝[≠] (e p), q ∈ e.target :=
    mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds (mem_chart_target _ p))
  obtain ⟨q, hq, hqt⟩ := (eventually_mem_nhdsWithin.and ht).exists
  refine ⟨⟨e.symm q, fun h => hq ?_⟩⟩
  have : q = e p := by rw [← h]; exact (e.right_inv hqt).symm
  exact this

/-- Path connectedness of the punctured manifold (`n ≥ 3`). -/
theorem pathConnected_compl_singleton [PathConnectedSpace M] (hn : 3 ≤ n) (p : M) :
    PathConnectedSpace {x : M // x ≠ p} := by
  have hne := nonempty_compl_singleton (n := n) (M := M) (by omega) p
  refine ⟨hne, fun x y => ?_⟩
  let γ₀ : Path x.1 y.1 := PathConnectedSpace.somePath x.1 y.1
  let H : C(I × I, M) := ⟨fun z => γ₀ z.1, γ₀.continuous.comp continuous_fst⟩
  let F : Set (I × I) := {z | z.1 = 0 ∨ z.1 = 1}
  have hF : IsClosed F :=
    (isClosed_eq continuous_fst continuous_const).union (isClosed_eq continuous_fst continuous_const)
  have hHF : ∀ z ∈ F, H z ≠ p := by
    rintro z (hz | hz)
    · show γ₀ z.1 ≠ p
      rw [hz, γ₀.source]; exact x.2
    · show γ₀ z.1 ≠ p
      rw [hz, γ₀.target]; exact y.2
  obtain ⟨H', hH'p, hH'F⟩ := pushoff M hn p H F hF hHF
  refine ⟨⟨⟨fun s => ⟨H' (s, 0), hH'p _⟩,
    (H'.continuous.comp (Continuous.prodMk_left 0)).subtype_mk _⟩, ?_, ?_⟩⟩
  · apply Subtype.ext
    show H' (0, 0) = x.1
    rw [hH'F (0, 0) (Or.inl rfl)]
    exact γ₀.source
  · apply Subtype.ext
    show H' (1, 0) = y.1
    rw [hH'F (1, 0) (Or.inr rfl)]
    exact γ₀.target

/-- Every loop in the punctured manifold is null-homotopic (`n ≥ 3`, `M` simply connected). -/
theorem loops_nullhomotopic [SimplyConnectedSpace M] (hn : 3 ≤ n) (p : M)
    (x : {x : M // x ≠ p}) (γ : Path x x) : γ.Homotopic (Path.refl x) := by
  have hM : (γ.map continuous_subtype_val).Homotopic (Path.refl x.1) :=
    SimplyConnectedSpace.paths_homotopic _ _
  obtain ⟨H₀⟩ := hM
  let F : Set (I × I) := {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1}
  have hF : IsClosed F :=
    (isClosed_eq continuous_fst continuous_const).union
      ((isClosed_eq continuous_fst continuous_const).union
        ((isClosed_eq continuous_snd continuous_const).union
          (isClosed_eq continuous_snd continuous_const)))
  have hHF : ∀ z ∈ F, H₀.toHomotopy.toContinuousMap z ≠ p := by
    rintro ⟨s, t⟩ (hs | hs | ht | ht)
    · simp only at hs; subst hs
      show H₀ (0, t) ≠ p
      rw [H₀.apply_zero]; exact (γ t).2
    · simp only at hs; subst hs
      show H₀ (1, t) ≠ p
      rw [H₀.apply_one]; exact x.2
    · simp only at ht; subst ht
      show H₀ (s, 0) ≠ p
      rw [H₀.source]; exact x.2
    · simp only at ht; subst ht
      show H₀ (s, 1) ≠ p
      rw [H₀.target]; exact x.2
  obtain ⟨H', hH'p, hH'F⟩ := pushoff M hn p H₀.toHomotopy.toContinuousMap F hF hHF
  refine ⟨{ toFun := fun z => ⟨H' z, hH'p z⟩
            continuous_toFun := H'.continuous.subtype_mk _
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    apply Subtype.ext
    show H' (0, t) = (γ t).1
    rw [hH'F (0, t) (Or.inl rfl)]
    exact H₀.apply_zero t
  · intro t
    apply Subtype.ext
    show H' (1, t) = x.1
    rw [hH'F (1, t) (Or.inr (Or.inl rfl))]
    exact H₀.apply_one t
  · intro t s hs
    apply Subtype.ext
    show H' (t, s) = (γ s).1
    rcases hs with rfl | rfl
    · rw [hH'F (t, 0) (Or.inr (Or.inr (Or.inl rfl))), γ.source]
      exact H₀.source t
    · rw [hH'F (t, 1) (Or.inr (Or.inr (Or.inr rfl))), γ.target]
      exact H₀.target t

end Assembly

/-- **Main theorem.** Removing a point from a simply connected topological `n`-manifold,
`n ≥ 3`, leaves a simply connected space. -/
theorem compl_singleton_simplyConnected (n : ℕ) (hn : 3 ≤ n) (M : Type*) [TopologicalSpace M]
    [T2Space M] [SimplyConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M) :
    SimplyConnectedSpace {x : M // x ≠ p} := by
  rw [simply_connected_iff_loops_nullhomotopic]
  exact ⟨pathConnected_compl_singleton hn p, fun x γ => loops_nullhomotopic hn p x γ⟩

end PushOff

/-- The target theorem. -/
theorem solution (n : ℕ) (hn : 3 ≤ n) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M) :
    SimplyConnectedSpace {x : M // x ≠ p} :=
  PushOff.compl_singleton_simplyConnected n hn M p
