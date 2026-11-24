-- Prove2me | solution 1 for TaoFivePrimes.theorem51_typeI_block_summation
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T11:31:56.592205+00:00
-- url     : https://prove2.me/submissions/ec3c57af-721b-4e9f-85b3-eb2837ded1c9

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Theorems.Thm_TaoFivePrimes_vinogradov_odd_sharp

set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

/-! # Type I block summation: reusable foundation, block structure, envelope

Reusable interface for the Prove2Me node
`TaoFivePrimes.theorem51_typeI_block_summation`, following Tao,
arXiv:1201.6656v4, Section 5, (5.14) → (5.17), and Section 2 (2.1).

Three layers, all `sorry`-free and Mathlib-only:
* **§1-5 foundation** — the distance to the nearest integer `rdist`, its
  triangle inequality, inequality (2.1), and the small-`d` core of (5.15)
  (`1/|sin (2πdα)| ≤ 2q` for `2d ≤ q`);
* **§6-7 block structure** — the block endpoints `2jq + q/2` and
  `2(j+1)q + q/2`, the bridge between the doubled integer spacing and the
  real block interval;
* **§8 frozen envelope** — the per-block domination of the pointwise
  envelope by its value frozen at the left endpoint;
* **§9-12 Corollary 3.5** — the floor helper lemmas, the index-set identity
  `2m+1 ∈ (x,y] ↔ m ∈ ((x-1)/2, (y-1)/2]`, the reindexing of the
  odd min-sum onto the full min-sum with parameter `2α` and phase
  `π α + θ`, and the resulting reduction of Corollary 3.5 to Lemma 3.4.

Design notes for this environment:

* no `conv`: rewriting under `abs`/`Real.sin` via `conv_rhs` exhausts the
  heartbeat budget.  Every step is an equality of *arguments* applied by
  `rw`;
* `linarith` cannot see through `Int.fract`/`Int.floor` casts, so each such
  bridge is a separate real-valued lemma;
* `linarith`/`nlinarith` treat `↑q / 2` as an opaque atom.  Endpoint
  statements are therefore *stated* in doubled integer form and halved
  once, after a `ring` normalization, by `div_lt_iff₀` / `le_div_iff₀`. -/

open Finset

namespace TaoFivePrimesBlock

/-! ## 1. Distance to the nearest integer -/

/-- Distance to the nearest integer, realized as the minimum of the two
complementary fractional parts, so that it lies in `[0, 1/2]`. -/
noncomputable def rdist (t : ℝ) : ℝ := min (Int.fract t) (1 - Int.fract t)

lemma rdist_eq_fract_or (t : ℝ) :
    rdist t = Int.fract t ∨ rdist t = 1 - Int.fract t :=
  min_choice _ _

lemma rdist_nonneg (t : ℝ) : 0 ≤ rdist t :=
  le_min (Int.fract_nonneg t) (by linarith [Int.fract_lt_one t])

lemma rdist_le_half (t : ℝ) : rdist t ≤ 1 / 2 := by
  have h1 := Int.fract_lt_one t
  rcases lt_or_ge (Int.fract t) (1 / 2) with h | h
  · exact (min_le_left _ _).trans h.le
  · exact (min_le_right _ _).trans (by linarith)

/-- Shifting by an integer multiple of `π` does not change `|sin|`. -/
lemma abs_sin_add_int_mul_pi (x : ℝ) (z : ℤ) :
    |Real.sin (x + (z : ℝ) * Real.pi)| = |Real.sin x| := by
  rw [Real.sin_add_int_mul_pi, abs_mul]
  simp [abs_zpow]

/-- `|sin|` is even. -/
lemma abs_sin_neg (x : ℝ) : |Real.sin (-x)| = |Real.sin x| := by
  rw [Real.sin_neg, abs_neg]

/-- `π · fract t` differs from `π t` by an integer multiple of `π`. -/
lemma pi_mul_fract_decomp (t : ℝ) :
    Real.pi * Int.fract t = Real.pi * t + ((-⌊t⌋ : ℤ) : ℝ) * Real.pi := by
  have hft : Int.fract t + (⌊t⌋ : ℝ) = t := Int.fract_add_floor t
  push_cast
  linear_combination Real.pi * hft

/-- `π · (fract t - 1)` differs from `π t` by an integer multiple of `π`. -/
lemma pi_mul_fract_sub_one_decomp (t : ℝ) :
    Real.pi * (Int.fract t - 1) = Real.pi * t + ((-(⌊t⌋ + 1) : ℤ) : ℝ) * Real.pi := by
  have hft : Int.fract t + (⌊t⌋ : ℝ) = t := Int.fract_add_floor t
  push_cast
  linear_combination Real.pi * hft

/-- **Phase reduction.** `sin (π ·)` only sees `rdist`. -/
lemma abs_sin_pi_eq_abs_sin_pi_rdist (t : ℝ) :
    |Real.sin (Real.pi * t)| = |Real.sin (Real.pi * rdist t)| := by
  rcases rdist_eq_fract_or t with h | h
  · rw [h, pi_mul_fract_decomp, abs_sin_add_int_mul_pi]
  · have hneg : Real.pi * (1 - Int.fract t) = -(Real.pi * (Int.fract t - 1)) := by ring
    rw [h, hneg, abs_sin_neg, pi_mul_fract_sub_one_decomp, abs_sin_add_int_mul_pi]

/-! ## 2. Inequality (2.1) -/

/-- **(2.1), lower half.** `2 ‖t‖_{R/Z} ≤ |sin (π t)|`. -/
theorem two_rdist_le_abs_sin (t : ℝ) : 2 * rdist t ≤ |Real.sin (Real.pi * t)| := by
  have key := abs_sin_pi_eq_abs_sin_pi_rdist t
  have hlow : 2 * rdist t ≤ |Real.sin (Real.pi * rdist t)| := by
    have hx : 0 ≤ Real.pi * rdist t := by nlinarith [Real.pi_pos, rdist_nonneg t]
    have hx' : Real.pi * rdist t ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos, rdist_le_half t]
    have hm := Real.mul_le_sin hx hx'
    have hsinpos : 0 ≤ Real.sin (Real.pi * rdist t) :=
      Real.sin_nonneg_of_mem_Icc ⟨hx, by linarith [Real.pi_pos]⟩
    rw [abs_of_nonneg hsinpos]
    have he : 2 / Real.pi * (Real.pi * rdist t) = 2 * rdist t := by field_simp
    linarith [hm, he.le]
  rw [key]
  exact hlow

/-- **(2.1), upper half.** `|sin (π t)| ≤ π ‖t‖_{R/Z}`. -/
theorem abs_sin_le_pi_mul_rdist (t : ℝ) :
    |Real.sin (Real.pi * t)| ≤ Real.pi * rdist t := by
  have key := abs_sin_pi_eq_abs_sin_pi_rdist t
  have hup : |Real.sin (Real.pi * rdist t)| ≤ Real.pi * rdist t := by
    have h := Real.abs_sin_le_abs (x := Real.pi * rdist t)
    have hnonneg : |Real.pi * rdist t| = Real.pi * rdist t :=
      abs_of_nonneg (by nlinarith [Real.pi_pos, rdist_nonneg t])
    linarith [h, hnonneg.le, hnonneg.ge]
  rw [key]
  exact hup

/-! ## 3. The arithmetic input of (5.15) -/

/-- `(m % q)/q + (m / q) = m/q` in `ℝ`, for `q ≠ 0`. -/
lemma div_q_eq (m q : ℤ) (hq : (q : ℝ) ≠ 0) :
    ((m % q : ℤ) : ℝ) / (q : ℝ) + ((m / q : ℤ) : ℝ) = (m : ℝ) / (q : ℝ) := by
  have h : m % q + q * (m / q) = m := Int.emod_add_mul_ediv m q
  have hR : ((m % q : ℤ) : ℝ) + (q : ℝ) * ((m / q : ℤ) : ℝ) = (m : ℝ) := by
    exact_mod_cast h
  rw [← hR, add_div]
  field_simp

/-- If `m/q` is not an integer then its nearest-integer distance is at least
`1/q`.  This is the arithmetic content of Tao's step (5.15). -/
lemma rdist_div_ge (m q : ℤ) (hq : 0 < q) (hm : ¬ (q ∣ m)) :
    1 / (q : ℝ) ≤ rdist ((m : ℝ) / (q : ℝ)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := hq0.ne'
  have hmod : Int.fract ((m : ℝ) / (q : ℝ)) = ((m % q : ℤ) : ℝ) / (q : ℝ) := by
    rw [Int.fract_eq_iff]
    have hmnn : (0 : ℝ) ≤ ((m % q : ℤ) : ℝ) := by
      exact_mod_cast Int.emod_nonneg m hq.ne'
    refine ⟨div_nonneg hmnn hq0.le, ?_, ?_⟩
    · rw [div_lt_one hq0]; exact_mod_cast Int.emod_lt_of_pos m hq
    · refine ⟨m / q, ?_⟩
      have h' := div_q_eq m q hqne
      rw [sub_eq_iff_eq_add, add_comm]
      exact h'.symm
  have hrem_pos : 0 < m % q := Int.emod_pos_of_not_dvd hm |>.resolve_left hq.ne'
  have hremr : (1 : ℝ) ≤ ((m % q : ℤ) : ℝ) := by exact_mod_cast hrem_pos
  have hleR : ((m % q : ℤ) : ℝ) + 1 ≤ (q : ℝ) := by
    exact_mod_cast (show m % q + 1 ≤ q by
      have := Int.emod_lt_of_pos m hq; omega)
  rw [rdist]
  apply le_min
  · have h : 1 / (q : ℝ) ≤ Int.fract ((m : ℝ) / (q : ℝ)) := by
      rw [hmod, div_le_div_iff_of_pos_right hq0]; exact hremr
    exact h
  · have h : 1 / (q : ℝ) ≤ 1 - Int.fract ((m : ℝ) / (q : ℝ)) := by
      rw [hmod, le_sub_iff_add_le]
      rw [← add_div]
      rw [div_le_one hq0]
      linarith
    exact h

/-! ## 4. The triangle inequality for `rdist`

`rdist` is the distance to the nearest integer, hence a genuine metric-like
pseudo-norm on `ℝ/ℤ`: `rdist (x + y) ≤ rdist x + rdist y`.  Everything is
reduced to the unit interval by subtracting the floors, which only shifts
`rdist` by an integer. -/

/-- In `[0,1)`, `Int.fract` is the identity. -/
lemma fract_eq_self {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : Int.fract u = u := by
  rw [Int.fract_eq_iff]; exact ⟨h0, h1, ⟨0, by simp⟩⟩

/-- `rdist (Int.fract t) = rdist t`. -/
lemma rdist_fract (t : ℝ) : rdist (Int.fract t) = rdist t := by
  unfold rdist; rw [Int.fract_fract]

/-- `rdist (x + y) = rdist (Int.fract x + Int.fract y)`. -/
lemma rdist_add_eq (x y : ℝ) :
    rdist (x + y) = rdist (Int.fract x + Int.fract y) := by
  have h : x + y = (Int.fract x + Int.fract y) + ((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ) := by
    have hx := Int.fract_add_floor x
    have hy := Int.fract_add_floor y
    push_cast
    linarith
  conv_lhs => rw [h]
  unfold rdist
  rw [Int.fract_add_intCast]

/-- On the unit interval, `rdist (u+v) ≤ rdist u + rdist v`; proved by splitting
on which of the two `rdist`-candidates for `u` and for `v` is realized. -/
lemma rdist_add_le_unit (u v : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) (hv : 0 ≤ v) (hv1 : v < 1) :
    rdist (u + v) ≤ rdist u + rdist v := by
  have hru : rdist u = min u (1 - u) := by unfold rdist; rw [fract_eq_self hu hu1]
  have hrv : rdist v = min v (1 - v) := by unfold rdist; rw [fract_eq_self hv hv1]
  rw [hru, hrv]
  rcases lt_or_ge (u + v) 1 with hlt | hge
  · have hf : rdist (u + v) = min (u + v) (1 - (u + v)) := by
      unfold rdist; rw [fract_eq_self (by linarith) hlt]
    rw [hf, min_le_iff]
    rcases min_choice u (1 - u) with hu' | hu' <;> rcases min_choice v (1 - v) with hv' | hv'
    · rw [hu', hv']; left; linarith
    · rw [hu', hv']; right; linarith
    · rw [hu', hv']; right; linarith
    · rw [hu', hv']; right
      have hle : 1 - u ≤ u := by rw [← hu']; exact min_le_left u (1 - u)
      linarith
  · have hfract2 : Int.fract (u + v) = u + v - 1 := by
      rw [Int.fract_eq_iff]; exact ⟨by linarith, by linarith, ⟨1, by ring⟩⟩
    have hf : rdist (u + v) = min (u + v - 1) (2 - (u + v)) := by
      unfold rdist; rw [hfract2]; ring_nf
    rw [hf, min_le_iff]
    rcases min_choice u (1 - u) with hu' | hu' <;> rcases min_choice v (1 - v) with hv' | hv'
    · rw [hu', hv']; left; linarith
    · rw [hu', hv']; left; linarith
    · rw [hu', hv']; left; linarith
    · rw [hu', hv']; right; linarith

/-- **Triangle inequality.** `rdist (x + y) ≤ rdist x + rdist y`. -/
lemma rdist_add_le' (x y : ℝ) : rdist (x + y) ≤ rdist x + rdist y := by
  rw [rdist_add_eq, ← rdist_fract x, ← rdist_fract y]
  exact rdist_add_le_unit _ _ (Int.fract_nonneg x) (Int.fract_lt_one x)
    (Int.fract_nonneg y) (Int.fract_lt_one y)

/-- `rdist t ≤ |t|`. -/
lemma rdist_le_abs (t : ℝ) : rdist t ≤ |t| := by
  have hf : Int.fract t = t - (⌊t⌋ : ℝ) := by
    have := Int.fract_add_floor t; linarith
  rcases lt_or_ge t 0 with h | h
  · rw [abs_of_neg h]
    have hfl : (⌊t⌋ : ℝ) ≤ -1 := by
      have hz : ⌊t⌋ < 0 := Int.floor_lt.mpr (by simpa using h)
      exact_mod_cast (show ⌊t⌋ ≤ -1 by omega)
    have hb : rdist t ≤ 1 - Int.fract t := min_le_right _ _
    rw [hf] at hb
    linarith
  · rw [abs_of_nonneg h]
    have hfl : (0 : ℝ) ≤ (⌊t⌋ : ℝ) := by
      have hz : (0 : ℤ) ≤ ⌊t⌋ := Int.le_floor.mpr (by simpa using h)
      exact_mod_cast hz
    have hb : rdist t ≤ Int.fract t := min_le_left _ _
    rw [hf] at hb
    linarith

/-- **1-Lipschitz form.** `rdist (x + y) ≤ rdist x + |y|`. -/
lemma rdist_add_le (x y : ℝ) : rdist (x + y) ≤ rdist x + |y| := by
  have h1 := rdist_add_le' x y
  have h2 := rdist_le_abs y
  linarith

/-- **Reverse triangle form** (Tao's (5.15)). `rdist y − rdist x ≤ |y − x|`. -/
lemma rdist_sub_le_abs_sub (x y : ℝ) : rdist y - rdist x ≤ |y - x| := by
  have h1 := rdist_add_le x (y - x)
  rw [add_sub_cancel] at h1
  have h2 : |y - x| = |x - y| := by rw [show y - x = -(x - y) by ring, abs_neg]
  linarith

/-- Shifted form used in (5.15): `rdist x − |e| ≤ rdist (x + e)`. -/
lemma rdist_sub_abs_le_add (x e : ℝ) : rdist x - |e| ≤ rdist (x + e) := by
  have h := rdist_sub_le_abs_sub (x + e) x
  rw [show x - (x + e) = -e by ring, abs_neg] at h
  -- rearrange `rdist x - rdist (x+e) ≤ |e|` into the stated form by hand,
  -- since `linarith` treats `rdist` as an opaque atom.
  have h' : rdist x ≤ rdist (x + e) + |e| := by linarith
  linarith

/-! ## 5. The small-`d` regime of (5.15) -/

/-- `|d·β| ≤ 1/(2q)` when `|β| ≤ 1/q²` and `2d ≤ q`. -/
lemma d_mul_beta_le (beta : ℝ) (q : ℝ) (hq : 0 < q) (hbeta : |beta| ≤ 1/q^2)
    (d : ℕ) (hd2 : (d : ℝ) * 2 ≤ q) :
    |(d : ℝ) * beta| ≤ 1/(2*q) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [abs_mul, abs_of_nonneg hd0]
  have h2 : (d : ℝ) * |beta| ≤ (d : ℝ) * (1/q^2) := mul_le_mul_of_nonneg_left hbeta hd0
  have key : (q/2) * (1/q^2) = 1/(2*q) := by field_simp
  calc (d : ℝ) * |beta| ≤ (d : ℝ) * (1/q^2) := h2
    _ ≤ (q/2) * (1/q^2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith [hd2]
    _ = 1/(2*q) := key

/-- **(5.15), quantitative core.** If `4α = a/q + β`, `|β| ≤ 1/q²`, `2d ≤ q` and
`q ∤ a d`, then `‖4 d α‖_{ℝ/ℤ} ≥ 1/(2q)`.  (Here `ad` plays the role of `a d`.) -/
lemma rdist_d_alpha_ge (ad q : ℤ) (alpha beta : ℝ)
    (hq : 0 < q) (hbeta : |beta| ≤ 1/(q:ℝ)^2) (hnondiv : ¬ (q ∣ ad))
    (d : ℕ) (_hd1 : 1 ≤ d) (hd2 : (d : ℝ) * 2 ≤ q)
    (hkey : 4 * (d : ℝ) * alpha = (ad : ℝ)/(q : ℝ) + (d : ℝ) * beta) :
    1/(2*(q:ℝ)) ≤ rdist (4 * (d : ℝ) * alpha) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h1 : 1/(q : ℝ) ≤ rdist ((ad : ℝ)/(q : ℝ)) := rdist_div_ge ad q hq hnondiv
  have h2 : |(d : ℝ) * beta| ≤ 1/(2*(q : ℝ)) :=
    d_mul_beta_le beta (q : ℝ) hqR hbeta d hd2
  rw [hkey]
  have h3 : 1/(q : ℝ) - |(d : ℝ) * beta|
      ≤ rdist ((ad : ℝ)/(q : ℝ) + (d : ℝ) * beta) := by
    have h5 := rdist_sub_abs_le_add ((ad : ℝ)/(q : ℝ)) ((d : ℝ) * beta)
    linarith [h1, h5]
  have h4 : 1/(2*(q : ℝ)) = 1/(q : ℝ) - 1/(2*(q : ℝ)) := by field_simp; ring
  linarith [h2, h4, h3]

/-! ## 6. The block index and its endpoints -/

/-- The left endpoint `2jq + q/2` of block `j`. -/
noncomputable def blockLeft (q : ℕ) (j : ℕ) : ℝ :=
  2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2

/-- The right endpoint `2(j+1)q + q/2` of block `j`. -/
noncomputable def blockRight (q : ℕ) (j : ℕ) : ℝ :=
  2 * ((j : ℝ) + 1) * (q : ℝ) + (q : ℝ) / 2

lemma blockRight_eq (q j : ℕ) : blockRight q j = blockLeft q (j + 1) := by
  unfold blockRight blockLeft
  push_cast
  ring

lemma blockRight_sub_blockLeft (q j : ℕ) : blockRight q j - blockLeft q j = 2 * (q : ℝ) := by
  unfold blockRight blockLeft
  ring

/-- `blockLeft` is strictly increasing in the block index when `q > 0`. -/
lemma blockLeft_lt_succ {q : ℕ} (hq : 0 < q) (j : ℕ) :
    blockLeft q j < blockLeft q (j + 1) := by
  unfold blockLeft
  push_cast
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  linarith

/-- Every block left endpoint is positive. -/
lemma blockLeft_pos {q : ℕ} (hq : 0 < q) (j : ℕ) : 0 < blockLeft q j := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  unfold blockLeft
  have key : 2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2
      = ((4 * (j : ℝ) * (q : ℝ)) + (q : ℝ)) / 2 := by ring
  rw [key]
  apply div_pos _ (by norm_num : (0 : ℝ) < 2)
  nlinarith

/-! ## 7. Membership in a block

The integer predicate `4jq + q < 2d ≤ 4(j+1)q + q` is the doubled form of
`blockLeft q j < d ≤ blockRight q j`. -/

/-- **Lower endpoint.** `4jq + q < 2d` halves to `blockLeft q j < d`. -/
lemma blockLeft_lt_of (q d j : ℕ) (h : 4 * j * q + q < 2 * d) :
    blockLeft q j < (d : ℝ) := by
  have hcast : ((4 * j * q + q : ℕ) : ℝ) < ((2 * d : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  unfold blockLeft
  have key : 2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2
      = ((4 * (j : ℝ) * (q : ℝ)) + (q : ℝ)) / 2 := by ring
  rw [key, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **Upper endpoint.** `2d ≤ 4(j+1)q + q` halves to `d ≤ blockRight q j`. -/
lemma le_blockRight_of (q d j : ℕ) (h : 2 * d ≤ 4 * (j + 1) * q + q) :
    (d : ℝ) ≤ blockRight q j := by
  have hcast : ((2 * d : ℕ) : ℝ) ≤ ((4 * (j + 1) * q + q : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  unfold blockRight
  have key : 2 * ((j : ℝ) + 1) * (q : ℝ) + (q : ℝ) / 2
      = ((4 * ((j : ℝ) + 1) * (q : ℝ)) + (q : ℝ)) / 2 := by ring
  rw [key, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **Block membership.** The doubled integer spacing is equivalent to the
real block interval `blockLeft q j < d ≤ blockRight q j`. -/
lemma mem_block_iff (q d j : ℕ) :
    (4 * j * q + q < 2 * d ∧ 2 * d ≤ 4 * (j + 1) * q + q)
      ↔ blockLeft q j < (d : ℝ) ∧ (d : ℝ) ≤ blockRight q j := by
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨blockLeft_lt_of q d j h1, le_blockRight_of q d j h2⟩
  · intro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have hR : ((4 * j * q + q : ℕ) : ℝ) < ((2 * d : ℕ) : ℝ) := by
        push_cast
        unfold blockLeft at h1
        linarith [h1]
      exact_mod_cast hR
    · have hR : ((2 * d : ℕ) : ℝ) ≤ ((4 * (j + 1) * q + q : ℕ) : ℝ) := by
        push_cast
        unfold blockRight at h2
        linarith [h2]
      exact_mod_cast hR

/-! ## 8. Freezing the `x/d` term at the left endpoint -/

/-- **Freeze step.** If `d` is in block `j` (so `blockLeft q j < d`) and
`d > 0`, then the first alternative of the node's envelope at `d` is at
most its value at the left endpoint:

`(1/2)(x/d) log x + 4 (log 2) log 2x ≤ x / (2 (2jq + q/2)) · log x + 4 (log 2) log 2x`

(the factor `2` in the denominator is the node's `1/2`, rewritten as
`x / (2 · blockLeft)`).  Requires `0 < x` and `0 ≤ log x` to keep the
direction of the comparison. -/
lemma freeze_x_div {q d j : ℕ} {x : ℝ}
    (hx : 0 < x) (hlx : 0 ≤ Real.log x) (hq : 0 < q)
    (hleft : blockLeft q j < (d : ℝ)) (_hd : 0 < (d : ℝ)) :
    (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      ≤ x / (2 * blockLeft q j) * Real.log x + 4 * Real.log 2 * Real.log (2 * x) := by
  have hbl : 0 < blockLeft q j := blockLeft_pos hq j
  -- `x/d ≤ x/blockLeft` because `blockLeft ≤ d` and `x > 0`
  have hdvd : x / (d : ℝ) ≤ x / blockLeft q j := by
    exact div_le_div_of_nonneg_left hx.le hbl hleft.le
  have hstep : (1 / 2) * (x / (d : ℝ)) ≤ x / (2 * blockLeft q j) := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    -- `x / (2 * bL) = (x / bL) / 2` and `(1/2) * (x/d) = (x/d)/2`
    have heq1 : x / (2 * blockLeft q j) = (x / blockLeft q j) / 2 := by
      rw [div_mul_eq_div_div, div_right_comm]
    have heq2 : (1 / 2) * (x / (d : ℝ)) = (x / (d : ℝ)) / 2 := by ring
    rw [heq1, heq2]
    exact div_le_div_of_nonneg_right hdvd h2.le
  have : (1 / 2) * (x / (d : ℝ)) * Real.log x
      ≤ x / (2 * blockLeft q j) * Real.log x :=
    mul_le_mul_of_nonneg_right hstep hlx
  linarith

/-- **Envelope domination.** Any `W` obeying the node's pointwise envelope
at `d` is bounded by either alternative.  This is the `min`-splitting used
to choose the second alternative on a block. -/
lemma envelope_le_second {x alpha : ℝ} {d : ℕ} {W : ℕ → ℝ}
    (hWb : W d ≤
      (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
        (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      else min ((1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
        (4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    W d ≤
      (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
        (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      else 4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|) := by
  refine hWb.trans ?_
  by_cases h : Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact min_le_right _ _

/-- **Frozen envelope, vanishing sine.** When `sin (2πdα) = 0` the node's
envelope is exactly the first alternative, and the freeze step bounds it by
the block's frozen first alternative. -/
lemma envelope_frozen_vanish {q d j : ℕ} {x alpha : ℝ} {W : ℕ → ℝ}
    (hx : 0 < x) (hlx : 0 ≤ Real.log x) (hq : 0 < q)
    (hleft : blockLeft q j < (d : ℝ)) (hd : 0 < (d : ℝ))
    (hsin : Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0)
    (hWb : W d ≤
      (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
        (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      else min ((1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
        (4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    W d ≤ x / (2 * blockLeft q j) * Real.log x + 4 * Real.log 2 * Real.log (2 * x) := by
  have h := hWb
  rw [if_pos hsin] at h
  exact h.trans (freeze_x_div hx hlx hq hleft hd)

/-- **Frozen envelope, nonvanishing sine.** When `sin (2πdα) ≠ 0` the node's
envelope is the `min` of the two alternatives, so it is dominated by the
block envelope: frozen first alternative in the first slot, the actual
cosecant term in the second. -/
lemma envelope_frozen_nonvanish {q d j : ℕ} {x alpha : ℝ} {W : ℕ → ℝ}
    (hx : 0 < x) (hlx : 0 ≤ Real.log x) (hq : 0 < q)
    (hleft : blockLeft q j < (d : ℝ)) (hd : 0 < (d : ℝ))
    (hsin : Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) ≠ 0)
    (hWb : W d ≤
      (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
        (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      else min ((1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
        (4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    W d ≤
      min (x / (2 * blockLeft q j) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
        (4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|) := by
  have h := hWb
  rw [if_neg hsin] at h
  exact h.trans (le_min ((min_le_left _ _).trans (freeze_x_div hx hlx hq hleft hd))
    (min_le_right _ _))

/-! ## 9. Floor helper lemmas for the reindexing -/

/-- If `1 ≤ ⌊y⌋₊` then `1 ≤ y`.  Used to make `Nat.floor_le` applicable to
`y` in the reindexing, where positivity of `y` is not a hypothesis but does
follow from the interval being nonempty. -/
lemma one_le_of_one_le_floor {y : ℝ} (h : 1 ≤ ⌊y⌋₊) : (1 : ℝ) ≤ y := by
  by_contra hc
  push_neg at hc
  have hz : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith : y < 1)
  omega

/-- `⌊y⌋₊ ≤ y` whenever `⌊y⌋₊ ≥ 1`; the positivity of `y` comes from the
previous lemma rather than being assumed. -/
lemma floor_le_of_one_le_floor {y : ℝ} (h : 1 ≤ ⌊y⌋₊) : (⌊y⌋₊ : ℝ) ≤ y :=
  Nat.floor_le (le_trans zero_le_one (one_le_of_one_le_floor h))

/-! ## 10. The reindexing `n = 2m + 1` -/

/-- **The index-set identity.**  For `1 ≤ x` and `m : ℕ`, the odd integer
`2m + 1` lies in `(x, y]` exactly when `m` lies in `((x-1)/2, (y-1)/2]`.

The hypothesis `1 ≤ x` is what makes `(x-1)/2 ≥ 0`, so that
`Nat.floor_lt` applies to `(x-1)/2`.  It is not removable: at `x = 0`,
`y = 1` the odd integer `1 = 2·0+1` lies in `(0, 1]` but the right-hand
side is `⌊-1/2⌋₊ < 0`, which is false. -/
lemma odd_mem_Ioc_iff (x y : ℝ) (hx : 1 ≤ x) (m : ℕ) :
    2 * m + 1 ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n.Coprime 2)
      ↔ ⌊(x - 1) / 2⌋₊ < m ∧ m ≤ ⌊(y - 1) / 2⌋₊ := by
  have hx0 : (0 : ℝ) ≤ (x - 1) / 2 := by linarith
  rw [Finset.mem_filter, Finset.mem_Ioc, Nat.coprime_two_right]
  constructor
  · rintro ⟨⟨h1, h2⟩, _hodd⟩
    have hfloor1 : 1 ≤ ⌊y⌋₊ := by omega
    have hy1 : (1 : ℝ) ≤ y := one_le_of_one_le_floor hfloor1
    have hy0 : (0 : ℝ) ≤ (y - 1) / 2 := by linarith
    constructor
    · rw [Nat.floor_lt hx0]
      have h1'' : ⌊x⌋₊ ≤ 2 * m := by omega
      have h1' : ((⌊x⌋₊ : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast h1''
      push_cast at h1'
      have hxlt := Nat.lt_floor_add_one x
      linarith
    · rw [Nat.le_floor_iff hy0]
      have h2' : ((2 * m + 1 : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h2
      push_cast at h2'
      linarith [floor_le_of_one_le_floor hfloor1]
  · rintro ⟨h1, h2⟩
    have hm1 : 1 ≤ m := Nat.lt_of_le_of_lt (Nat.zero_le _) h1
    have hy0 : (0 : ℝ) ≤ (y - 1) / 2 := by
      -- `m ≥ 1` and `m ≤ ⌊(y-1)/2⌋₊`, so `(y-1)/2 ≥ 1`
      have hfloor1 : 1 ≤ ⌊(y - 1) / 2⌋₊ := le_trans hm1 h2
      have hstep : (1 : ℝ) ≤ (y - 1) / 2 := one_le_of_one_le_floor hfloor1
      linarith
    constructor
    · constructor
      · -- `⌊x⌋₊ < 2m + 1`
        have hm : ((x - 1) / 2 : ℝ) < (m : ℝ) := (Nat.floor_lt hx0).mp h1
        have hx' : x < ((2 * m + 1 : ℕ) : ℝ) := by push_cast; linarith
        -- `⌊x⌋₊ ≤ x < 2m+1` in `ℕ`, so `⌊x⌋₊ ≤ 2m`
        have hxle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
        have h2m : ((2 * m : ℕ) : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by push_cast; linarith
        have : (⌊x⌋₊ : ℕ) < 2 * m + 1 := by
          have hR : ((⌊x⌋₊ : ℕ) : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by linarith
          exact_mod_cast hR
        omega
      · -- `2m + 1 ≤ ⌊y⌋₊`
        have hm : (m : ℝ) ≤ (y - 1) / 2 := (Nat.le_floor_iff hy0).mp h2
        have hy : ((2 * m + 1 : ℕ) : ℝ) ≤ y := by push_cast; linarith
        exact Nat.le_floor hy
    · exact ⟨m, by ring⟩

/-! ## 11. The reindexing as a sum identity -/

/-- **The reindexing step.** `n = 2m + 1` turns the odd min-sum with
`α` and phase `θ` into the full min-sum with `2α` and phase `π α + θ`.
This is the entire content of the proof of Corollary 3.5.

The identity is stated with `1 ≤ x`, which the index-set identity requires;
in every application `x ≥ 1` (the summations start at `d = 1`). -/
lemma odd_min_sum_reindex (A B alpha theta : ℝ) (x y : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n.Coprime 2),
        min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|))
      = ∑ m ∈ Finset.Ioc ⌊(x - 1) / 2⌋₊ ⌊(y - 1) / 2⌋₊,
          min A (B / |Real.sin (Real.pi * (2 * alpha) * (m : ℝ)
            + (Real.pi * alpha + theta))|) := by
  refine Finset.sum_bij (fun n _ => (n - 1) / 2) ?_ ?_ ?_ ?_
  · -- the image lands in the target index set
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, hcop⟩ := hn
    have hodd : Odd n := Nat.coprime_two_right.mp hcop
    -- `n` is odd, so `n = 2k + 1`; then `(n-1)/2 = k`
    obtain ⟨k, hk⟩ := hodd
    rw [Finset.mem_Ioc]
    have hkx : (n - 1) / 2 = k := by omega
    rw [hkx]
    -- translate `⌊x⌋₊ < n = 2k+1 ≤ ⌊y⌋₊` into the `k`-range
    have hk1 : ((x - 1) / 2 : ℝ) < (k : ℝ) := by
      have hx0 : (0 : ℝ) ≤ (x - 1) / 2 := by linarith
      have hxl : ⌊x⌋₊ ≤ 2 * k := by omega
      have hcast : ((⌊x⌋₊ : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast hxl
      push_cast at hcast
      have hxlt := Nat.lt_floor_add_one x
      linarith
    have hk2 : (k : ℝ) ≤ (y - 1) / 2 := by
      have hy0 : (0 : ℝ) ≤ (y - 1) / 2 := by
        have hfloor1 : 1 ≤ ⌊y⌋₊ := by omega
        have := one_le_of_one_le_floor hfloor1
        linarith
      have h2' : ((2 * k + 1 : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
        exact_mod_cast (show 2 * k + 1 ≤ ⌊y⌋₊ by omega)
      push_cast at h2'
      linarith [floor_le_of_one_le_floor (show 1 ≤ ⌊y⌋₊ by omega)]
    constructor
    · exact (Nat.floor_lt (by linarith : (0 : ℝ) ≤ (x - 1) / 2)).mpr hk1
    · exact Nat.le_floor hk2
  · -- injectivity
    intro n hn n' hn' heq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn hn'
    obtain ⟨⟨_, _⟩, hcop⟩ := hn
    obtain ⟨⟨_, _⟩, hcop'⟩ := hn'
    obtain ⟨k, hk⟩ := Nat.coprime_two_right.mp hcop
    obtain ⟨k', hk'⟩ := Nat.coprime_two_right.mp hcop'
    have h1 : (n - 1) / 2 = k := by omega
    have h2 : (n' - 1) / 2 = k' := by omega
    omega
  · -- surjectivity
    intro m hm
    refine ⟨2 * m + 1, ?_, ?_⟩
    · have hmem : 2 * m + 1 ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n.Coprime 2) :=
        (odd_mem_Ioc_iff x y hx m).mpr (Finset.mem_Ioc.mp hm)
      exact hmem
    · show (2 * m + 1 - 1) / 2 = m
      omega
  · -- the summands agree
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨_, _⟩, hcop⟩ := hn
    obtain ⟨k, hk⟩ := Nat.coprime_two_right.mp hcop
    rw [hk, show (2 * k + 1 - 1) / 2 = k by omega]
    congr 1
    push_cast
    ring

/-! ## 12. The published statements as reusable `Prop`s

Both Lemma 3.4 and Corollary 3.5 are stated as `Prop`-valued definitions so
that they can be cited, instantiated, and reused across modules without
repeating the long Finset expression.  The **content** of Lemma 3.4 is the
classical Vinogradov bound and is carried as a hypothesis of the reduction
below; only the reindexing (the passage from Corollary 3.5 to Lemma 3.4) is
proved here. -/

/-- **Lemma 3.4 (Vinogradov-type lemma).**  The full-sum bound, with the
summation variable an integer `n` in the half-open interval `(x, y]`, phase
`π α n + θ`, and `⌊(y-x)/q⌋ + 1` blocks of length `q`.

This is the published input; it is *not* re-proved here. -/
def vinogradovMinSum (q : ℕ) (A B alpha theta x y : ℝ) : Prop :=
  (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|))
    ≤ (((⌊(y - x) / (q : ℝ)⌋₊ + 1 : ℕ)) : ℝ)
        * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)))

/-- **Corollary 3.5 (restricting to odd integers).**  The odd-sum bound: the
summand is the same `min` expression, restricted to odd `n` in `(x, y]`, and
the block count is `⌊(y-x)/(2q)⌋ + 1` — the factor of two coming from the odd
restriction. -/
def vinogradovMinSumOdd (q : ℕ) (A B alpha theta x y : ℝ) : Prop :=
  (∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => n.Coprime 2),
      min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|))
    ≤ (((⌊(y - x) / (2 * (q : ℝ))⌋₊ + 1 : ℕ)) : ℝ)
        * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ)))

/-- **Corollary 3.5 from Lemma 3.4.**  The odd-restricted min-sum with
parameter `α` and phase `θ` is bounded by applying the Vinogradov bound to
the *full* interval with parameter `2α`, phase `π α + θ`, and the shifted
endpoints `(x-1)/2`, `(y-1)/2`.

The proof is the reindexing `n = 2m + 1` (`odd_min_sum_reindex`) together
with the arithmetic identity `(y - x)/(2q) = ((y-1)/2 - (x-1)/2)/q`, which
makes the two block counts agree.  Only the *index arithmetic* is proved
here; the analytic content of Lemma 3.4 stays a hypothesis. -/
theorem odd_vinogradov_min_sum (q : ℕ) (A B alpha theta x y : ℝ) (hx : 1 ≤ x)
    (hmain : vinogradovMinSum q A B (2 * alpha) (Real.pi * alpha + theta)
      ((x - 1) / 2) ((y - 1) / 2)) :
    vinogradovMinSumOdd q A B alpha theta x y := by
  unfold vinogradovMinSumOdd vinogradovMinSum at *
  rw [odd_min_sum_reindex A B alpha theta x y hx]
  -- The two block counts agree because `(y-x)/(2q) = ((y-1)/2-(x-1)/2)/q`.
  have hkey : (y - x) / (2 * (q : ℝ))
      = ((y - 1) / 2 - (x - 1) / 2) / (q : ℝ) := by ring
  rw [hkey]
  exact hmain

/-! ## 6. From (2.1)'s lower half to a cosecant bound -/

/-- **(2.1) + an explicit positive lower bound on `rdist`.**  If
`1/(2 r) ≤ rdist t` and `r > 0`, then `|sin (π t)| ≥ 1/r`; equivalently
`1 / |sin (π t)| ≤ r`.

The hypothesis `hr : 0 < r` is essential: it is what makes `rdist t`
strictly positive, and without it the reciprocal bound is false (take
`rdist t = 0`). -/
lemma inv_abs_sin_le_of_rdist_ge (t r : ℝ) (hr : 0 < r)
    (h : 1 / (2 * r) ≤ rdist t) :
    1 / |Real.sin (Real.pi * t)| ≤ r := by
  have hpos : 0 < rdist t := lt_of_lt_of_le (by positivity) h
  have hsin : 1 / r ≤ |Real.sin (Real.pi * t)| := by
    have h2 := two_rdist_le_abs_sin t
    have h3 : 2 * (1 / (2 * r)) ≤ 2 * rdist t :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    have h4 : 1 / r = 2 * (1 / (2 * r)) := by field_simp
    calc 1 / r = 2 * (1 / (2 * r)) := h4
      _ ≤ 2 * rdist t := h3
      _ ≤ |Real.sin (Real.pi * t)| := h2
  have hfinal := one_div_le_one_div_of_le (one_div_pos.mpr hr) hsin
  rwa [one_div_one_div] at hfinal

end TaoFivePrimesBlock

/-! # Type I block summation: the assembly (Child 2)

Tao, arXiv:1201.6656v4, Section 5.2, the passage from (5.14) to (5.17).

This module is the second child of `TaoFivePrimes.theorem51_typeI_block_summation`.
It combines

* the reusable foundation `Definitions.Def_TaoFivePrimes_BlockFoundation`
  (`rdist`, inequality (2.1), the small-`d` core (5.15)-(5.16), the block
  structure, the frozen envelope, and the Corollary 3.5 reindexing), with
* the platform's divisor interface `TaoFivePrimes.theorem51Divisors`,

to bound the whole envelope sum.  Every step of Tao's own split is a separate
lemma; see the per-section comments below.

All declarations are `sorry`-free and Mathlib-only. -/

open Finset

namespace TaoFivePrimesAssembly

/-! ## 1. Coprimality transfer: `q ⊥ a` and `q ∤ d` give `q ∤ a d` -/

/-- **Coprimality transfer.**  If `q` is coprime to `a.natAbs` and does not
divide `d`, then `q` does not divide the integer product `a d`.  This is the
bridge that turns the parent's `Nat.Coprime a.natAbs q` into the
`¬ (q ∣ ad)` hypothesis of `rdist_d_alpha_ge`. -/
lemma not_dvd_mul_of_coprime {a : ℤ} {q d : ℕ} (hcop : Nat.Coprime a.natAbs q)
    (hd : ¬ (q ∣ d)) : ¬ ((q : ℤ) ∣ a * (d : ℤ)) := by
  intro h
  apply hd
  have h1 : ((q : ℤ)).natAbs ∣ (a * (d : ℤ)).natAbs := Int.natAbs_dvd_natAbs.mpr h
  rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at h1
  exact hcop.symm.dvd_of_dvd_mul_left h1

/-- A positive integer strictly below `q` is not divisible by `q`. -/
lemma not_dvd_of_lt {d q : ℕ} (hpos : 0 < d) (hlt : d < q) : ¬ (q ∣ d) := by
  intro h
  have := Nat.le_of_dvd hpos h
  omega

/-! ## 2. The pointwise cosecant bound on the small-`d` range

`rdist_d_alpha_ge` (from the foundation) gives `‖4dα‖_{ℝ/ℤ} ≥ 1/(2q)`, and
`inv_abs_sin_le_of_rdist_ge` turns that into `1/|sin(π·4dα)| ≤ q`.  This is
Tao's (5.16), with `q` in place of his `2q` (his `2q` is the weaker bound
obtained from `1/|sin(π/4q)| ≤ 2q`). -/

/-- **(5.16).**  If `4α = a/q + β` with `|β| ≤ q^{-2}`, `q ≥ 1`, `q ⊥ a`,
`0 < d ≤ q/2` and `d < q`, then `1/|sin (4πdα)| ≤ q`. -/
lemma small_d_cosec_le (q : ℕ) (alpha beta : ℝ) (a : ℤ) (hq : 0 < q)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) (hcop : Nat.Coprime a.natAbs q)
    (d : ℕ) (hd1 : 1 ≤ d) (hd2 : (d : ℝ) * 2 ≤ (q : ℝ)) (hdlt : d < q)
    (hkey : 4 * (d : ℝ) * alpha = (a : ℝ) * (d : ℝ) / (q : ℝ) + (d : ℝ) * beta) :
    1 / |Real.sin (Real.pi * (4 * (d : ℝ) * alpha))| ≤ (q : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hnd : ¬ ((q : ℤ) ∣ a * (d : ℤ)) :=
    not_dvd_mul_of_coprime hcop (not_dvd_of_lt (by omega) hdlt)
  have h := TaoFivePrimesBlock.rdist_d_alpha_ge (a * (d : ℤ)) (q : ℤ) alpha beta
    (by exact_mod_cast hq) (by push_cast; exact hbeta) hnd d hd1 hd2
    (by push_cast; linarith [hkey])
  exact TaoFivePrimesBlock.inv_abs_sin_le_of_rdist_ge (4 * (d : ℝ) * alpha) (q : ℝ) hqR h

/-! ## 3. The integral test (Tao's evaluation `Σ_{0≤j} x/(2jq+q/2) ≤ x/2q log(2UV/q+4)`)

The sum `Σ_{0 ≤ j ≤ J} x/(2jq + q/2)` is bounded by the integral of
`x/(2tq + q/2)` over `[0, J]` plus the `j = 0` term.  Because the summand is
antitone, `AntitoneOn.sum_le_integral` applies after shifting: the sum over
`range (J+1)` splits into `j = 0` (worth `2x/q`) plus `Σ_{i<J} h(i+1)`, and the
latter is at most `∫_0^J h`.  Evaluating that integral gives
`(x/2q) log(4J + 1)`, and with `J = ⌊UV/2q − 1/4⌋₊` this is
`(x/2q) log(2UV/q + 4)` up to the rounding recorded in §5. -/

/-- The antitone integrand of the integral test, on `Icc 0 J`. -/
lemma antitoneOn_assembly (x q : ℝ) (hx : 0 < x) (hq : 0 < q) (J : ℕ) :
    AntitoneOn (fun t : ℝ => x / (2 * t * q + q / 2)) (Set.Icc (0 : ℝ) (0 + (J : ℝ))) := by
  intro u hu v _ huv
  have h1 : 0 < 2 * u * q + q / 2 := by have : (0 : ℝ) ≤ u := hu.1; nlinarith
  have h2 : 0 < 2 * v * q + q / 2 := by have : (0 : ℝ) ≤ v := le_trans hu.1 huv; nlinarith
  apply div_le_div_of_nonneg_left hx.le h1
  nlinarith

/-- `∫ t in a..b, 1/(t + 1/4) = log ((b + 1/4)/(a + 1/4))`. -/
lemma integral_inv_shift (a b : ℝ) (hab : (0 : ℝ) ∉ Set.uIcc (a + 1 / 4) (b + 1 / 4)) :
    ∫ t in a..b, (1 : ℝ) / (t + 1 / 4) = Real.log ((b + 1 / 4) / (a + 1 / 4)) := by
  have h := intervalIntegral.integral_comp_add_right (a := a) (b := b)
    (f := fun u : ℝ => (1 : ℝ) / u) (1 / 4)
  rw [h]
  have h2 : ∫ u in (a + 1 / 4)..(b + 1 / 4), (1 : ℝ) / u
      = ∫ u in (a + 1 / 4)..(b + 1 / 4), u⁻¹ := by
    apply intervalIntegral.integral_congr
    intro u _
    simp [one_div]
  rw [h2, integral_inv hab]

/-- **Integral evaluation.**  `∫_0^J x/(2tq + q/2) dt = (x/2q) log(4J + 1)`. -/
lemma integral_assembly (x q : ℝ) (hx : 0 < x) (hq : 0 < q) (J : ℕ) :
    ∫ t in (0 : ℝ)..(J : ℝ), x / (2 * t * q + q / 2)
      = (x / (2 * q)) * Real.log (((J : ℝ) + 1 / 4) / (1 / 4)) := by
  have hsplit : ∫ t in (0 : ℝ)..(J : ℝ), x / (2 * t * q + q / 2)
      = (x / (2 * q)) * ∫ t in (0 : ℝ)..(J : ℝ), (1 : ℝ) / (t + 1 / 4) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    have hq' : q ≠ 0 := ne_of_gt hq
    field_simp
    ring
  rw [hsplit]
  have h0 : (0 : ℝ) ∉ Set.uIcc (0 + 1 / 4) ((J : ℝ) + 1 / 4) := by
    rw [Set.uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) J])]
    intro h
    rw [Set.mem_Icc] at h
    linarith [h.1]
  rw [integral_inv_shift (0 : ℝ) (J : ℝ) h0]
  ring_nf

/-- **The integral test.**  For `0 < x`, `0 < q`,
`Σ_{0 ≤ j ≤ J} x/(2jq + q/2) ≤ (x/2q) log(4J + 1) + 2x/q`, the `+2x/q` being
exactly the retained `j = 0` term that Tao's display `log(2UV/q+4)` restores. -/
lemma integral_test (x q : ℝ) (hx : 0 < x) (hq : 0 < q) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), x / (2 * (j : ℝ) * q + q / 2))
      ≤ (x / (2 * q)) * Real.log (((J : ℝ) + 1 / 4) / (1 / 4)) + x / (q / 2) := by
  have hanti := antitoneOn_assembly x q hx hq J
  have hmono := AntitoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := J)
    (f := fun t : ℝ => x / (2 * t * q + q / 2)) hanti
  simp only [zero_add] at hmono
  have hsplit : (∑ j ∈ Finset.range (J + 1), x / (2 * (j : ℝ) * q + q / 2))
      = (∑ i ∈ Finset.range J, x / (2 * ((i : ℝ) + 1) * q + q / 2)) + x / (q / 2) := by
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      congr 3
      push_cast
      ring
    · norm_num
  rw [hsplit]
  have hmain : (∑ i ∈ Finset.range J, x / (2 * ((i : ℝ) + 1) * q + q / 2))
      ≤ ∫ t in (0 : ℝ)..(J : ℝ), x / (2 * t * q + q / 2) := by
    refine le_trans (le_of_eq ?_) hmono
    apply Finset.sum_congr rfl
    intro i _
    congr 3
    push_cast
    ring
  linarith [hmain, integral_assembly x q hx hq J]

/-! ## 4. The block family

Tao's block `j` is `2jq + q/2 < d ≤ 2(j+1)q + q/2`; in the doubled integer
form used throughout the foundation this is `4jq + q < 2d ≤ 4(j+1)q + q`.
As a `Finset` of natural numbers the block is therefore
`Ioc ⌊(4jq+q)/2⌋ ⌊(4(j+1)q+q)/2⌋`, and the halvings are `Nat.div`
(so the endpoints are exact integers, no real rounding is involved).

The three facts needed for the assembly are: the doubled/integer equivalence
(`mem_blockFinset_iff`), that the blocks are pairwise disjoint
(`blockFinset_disjoint`), and that they telescope to the whole range
`(q/2, (4(J+1)q+q)/2]` (`biUnion_blockFinset`). -/

/-- Block `j` of the range, as a set of integers: the doubled form of
`2jq + q/2 < d ≤ 2(j+1)q + q/2`. -/
noncomputable def blockFinset (q j : ℕ) : Finset ℕ :=
  Finset.Ioc ((4 * j * q + q) / 2) ((4 * (j + 1) * q + q) / 2)

/-- **Doubled/integer equivalence.**  `d` lies in `blockFinset q j` exactly when
`4jq + q < 2d ≤ 4(j+1)q + q`, which is the doubled form of the real block
interval `blockLeft q j < d ≤ blockRight q j` (cf. `mem_block_iff`). -/
lemma mem_blockFinset_iff (q j d : ℕ) :
    d ∈ blockFinset q j ↔ 4 * j * q + q < 2 * d ∧ 2 * d ≤ 4 * (j + 1) * q + q := by
  unfold blockFinset
  rw [Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)] at h1; omega,
           by rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)] at h2; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]; omega,
           by rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]; omega⟩

/-- `m < (⌊m/k⌋ + 1) * k` for `k > 0`; the strict form of `Nat.div_add_mod`. -/
lemma lt_div_add_one_mul (m k : ℕ) (hk : 0 < k) : m < (m / k + 1) * k := by
  have h := Nat.div_add_mod m k
  have hmod := Nat.mod_lt m hk
  nlinarith [h, hmod]

/-- **Coverage.**  Any `d` with `2d > q` lies in the block with index
`⌊(2d − q − 1)/(4q)⌋`.  The `− 1` is essential: with `⌊(2d−q)/(4q)⌋` the
statement fails at `q = 4`, `d = 10` (that index gives block `1`, whose left
endpoint is `20 > 10`). -/
lemma mem_blockFinset_index (q d : ℕ) (hq : 0 < q) (hd : q < 2 * d) :
    d ∈ blockFinset q ((2 * d - q - 1) / (4 * q)) := by
  rw [mem_blockFinset_iff]
  have h4q : 0 < 4 * q := by omega
  have hid1 : 4 * ((2 * d - q - 1) / (4 * q)) * q
      = ((2 * d - q - 1) / (4 * q)) * (4 * q) := by ring
  have hid2 : 4 * ((2 * d - q - 1) / (4 * q) + 1) * q
      = ((2 * d - q - 1) / (4 * q) + 1) * (4 * q) := by ring
  have hle := Nat.div_mul_le_self (2 * d - q - 1) (4 * q)
  have hlt := lt_div_add_one_mul (2 * d - q - 1) (4 * q) h4q
  constructor <;> omega

/-- **Uniqueness.**  At most one block contains a given `d`: the block index is
strictly increasing, with gap `2q` in the doubled coordinate. -/
lemma blockFinset_unique (q d j j' : ℕ)
    (h : d ∈ blockFinset q j) (h' : d ∈ blockFinset q j') : j = j' := by
  rw [mem_blockFinset_iff] at h h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hmono : 4 * (j + 1) * q ≤ 4 * j' * q := by
      have : j + 1 ≤ j' := hlt
      nlinarith
    omega
  · have hmono : 4 * (j' + 1) * q ≤ 4 * j * q := by
      have : j' + 1 ≤ j := hgt
      nlinarith
    omega

/-- Blocks with different indices are disjoint. -/
lemma blockFinset_disjoint (q j j' : ℕ) (h : j ≠ j') :
    Disjoint (blockFinset q j) (blockFinset q j') := by
  rw [Finset.disjoint_left]
  intro d hd hd'
  exact h (blockFinset_unique q d j j' hd hd')

/-- **Telescoping.**  The blocks `0, …, J` tile the whole range
`(⌊q/2⌋, ⌊(4(J+1)q+q)/2⌋]` — each block's right endpoint is the next block's
left endpoint, so the union is a single interval. -/
lemma biUnion_blockFinset (q J : ℕ) :
    (Finset.range (J + 1)).biUnion (fun j => blockFinset q j)
      = Finset.Ioc (q / 2) ((4 * (J + 1) * q + q) / 2) := by
  have hle : ∀ n : ℕ, q / 2 ≤ (4 * (n + 1) * q + q) / 2 := by
    intro n
    apply Nat.div_le_div_right
    have h : 4 * (n + 1) * q = 4 * ((n + 1) * q) := by ring
    nlinarith [Nat.zero_le n, Nat.zero_le q]
  have hle' : ∀ n : ℕ,
      (4 * (n + 1) * q + q) / 2 ≤ (4 * (n + 1 + 1) * q + q) / 2 := by
    intro n
    apply Nat.div_le_div_right
    have h : 4 * (n + 1 + 1) * q = 4 * (n + 1) * q + 4 * q := by ring
    nlinarith [Nat.zero_le q]
  induction J with
  | zero => simp [blockFinset]
  | succ n ih =>
    have hsucc : blockFinset q (n + 1)
        = Finset.Ioc ((4 * (n + 1) * q + q) / 2) ((4 * (n + 1 + 1) * q + q) / 2) := by
      simp only [blockFinset, Nat.add_assoc]
    rw [Finset.range_add_one, Finset.biUnion_insert, ih, hsucc, Finset.union_comm,
        Finset.Ioc_union_Ioc_eq_Ioc (hle n) (hle' n)]

/-! ## 5. The two envelope alternatives, and their sum

The node's envelope is written as an `if` on the vanishing of the sine wrapping
a `min`.  For the assembly it is convenient to split it additively: the first
alternative `env1` (the `x/d` term plus the constant `4 log 2 · log 2x`) and
the second `env2` (the cosecant term, with the same constant in the numerator).

`envelope_le_sum` is the only place the `if` is opened; after it, every
estimate is on the two additive pieces separately, which is what makes the
small-`d` range and each block independently bounded. -/

/-- First envelope alternative: `½·(x/d)·log x + 4(log 2)·log 2x`. -/
noncomputable def env1 (x : ℝ) (d : ℕ) : ℝ :=
  (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)

/-- Second envelope alternative: `4(log 2)·log 2x / |sin (2πdα)|`. -/
noncomputable def env2 (alpha x : ℝ) (d : ℕ) : ℝ :=
  4 * Real.log 2 * Real.log (2 * x)
    / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|

/-- `log 2 ≥ 0`, used everywhere the envelope's constant appears. -/
lemma log_two_nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)

/-- **Additive envelope split.**  Any `W` obeying the node's pointwise
`if … then … else min …` envelope is bounded by `env1 + env2`.  The `if` is
opened exactly once here; the two alternatives are then never separated. -/
lemma envelope_le_sum (alpha x : ℝ) (d : ℕ) (W : ℕ → ℝ) (hx : 1 ≤ x)
    (h : W d ≤ if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0
              then env1 x d else min (env1 x d) (env2 alpha x d)) :
    W d ≤ env1 x d + env2 alpha x d := by
  have h1 : (0 : ℝ) ≤ Real.log 2 := log_two_nonneg
  have h2 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have he2 : 0 ≤ env2 alpha x d := by
    unfold env2
    exact div_nonneg (by positivity) (abs_nonneg _)
  have hle : min (env1 x d) (env2 alpha x d) ≤ env1 x d + env2 alpha x d :=
    le_trans (min_le_left _ _)
      (by linarith [min_le_right (env1 x d) (env2 alpha x d)])
  split_ifs at h with hs
  · exact le_trans h (by linarith)
  · exact le_trans h hle

/-- `env1` is nonnegative in the regime `x ≥ 1`, `d ≥ 1`. -/
lemma env1_nonneg (x : ℝ) (d : ℕ) (hx : 1 ≤ x) (hd : 1 ≤ d) :
    0 ≤ env1 x d := by
  have h1 : (0 : ℝ) ≤ Real.log 2 := log_two_nonneg
  have h2 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hx' : (0 : ℝ) < x := by linarith
  unfold env1
  have : 0 ≤ (1 / 2) * (x / (d : ℝ)) * Real.log x := by
    apply mul_nonneg
    · apply mul_nonneg (by norm_num)
      exact div_nonneg hx'.le hd'.le
    · exact Real.log_nonneg hx
  linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (mul_nonneg h1 h2)]

/-- `env2` is nonnegative, provided the envelope's log factor is. -/
lemma env2_nonneg (alpha x : ℝ) (d : ℕ) (hx : 1 ≤ 2 * x) : 0 ≤ env2 alpha x d := by
  unfold env2
  refine div_nonneg ?_ (abs_nonneg _)
  have h1 : (0 : ℝ) ≤ Real.log 2 := log_two_nonneg
  have h2 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg hx
  nlinarith [mul_nonneg h1 h2]

end TaoFivePrimesAssembly

namespace TaoFivePrimesSol


/-! ## Stage 1: reusable analytic helpers -/

/-- `sin (π t) ≠ 0` when `rdist t > 0`. -/
lemma sin_pi_ne_zero_of_rdist_pos {t : ℝ} (h : 0 < TaoFivePrimesBlock.rdist t) :
    Real.sin (Real.pi * t) ≠ 0 := by
  intro hsin
  have hlow := TaoFivePrimesBlock.two_rdist_le_abs_sin t
  rw [hsin, abs_zero] at hlow
  linarith

/-- Harmonic bound for the block sum `Σ_{j<J+1} x/bl_j`, with `bl_j` the left
endpoint `2jq + q/2` of block `j`. -/
lemma blocksum_le (x : ℝ) (q : ℕ) (M : ℝ) (hx : 0 < x) (hq : 0 < q)
    (J : ℕ) (hJ : 4 * (J : ℝ) ≤ 2 * M / (q : ℝ)) :
    (∑ j ∈ Finset.range (J + 1), x / TaoFivePrimesBlock.blockLeft q j)
      ≤ (x / (2 * (q : ℝ))) * (Real.log (2 * M / (q : ℝ) + 4) + 4) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h := TaoFivePrimesAssembly.integral_test x (q : ℝ) hx hqR J
  have harg : ∀ j : ℕ,
      x / (2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2)
        = x / TaoFivePrimesBlock.blockLeft q j := by
    intro j
    unfold TaoFivePrimesBlock.blockLeft
    ring_nf
  rw [Finset.sum_congr rfl (fun j _ => harg j)] at h
  have h4J : 4 * (J : ℝ) + 1 ≤ 2 * M / (q : ℝ) + 4 := by linarith
  have hlog : Real.log (4 * (J : ℝ) + 1) ≤ Real.log (2 * M / (q : ℝ) + 4) :=
    Real.log_le_log (by linarith) h4J
  have hlogeq : ((J : ℝ) + 1 / 4) / (1 / 4) = 4 * (J : ℝ) + 1 := by ring
  rw [hlogeq] at h
  have hxq : x / ((q : ℝ) / 2) = 2 * x / (q : ℝ) := by ring
  rw [hxq] at h
  have hfac : (0 : ℝ) ≤ x / (2 * (q : ℝ)) := by positivity
  calc (∑ j ∈ Finset.range (J + 1), x / TaoFivePrimesBlock.blockLeft q j)
      ≤ (x / (2 * (q : ℝ))) * Real.log (4 * (J : ℝ) + 1) + 2 * x / (q : ℝ) := h
    _ ≤ (x / (2 * (q : ℝ))) * Real.log (2 * M / (q : ℝ) + 4) + 2 * x / (q : ℝ) := by
        have := mul_le_mul_of_nonneg_left hlog hfac
        linarith
    _ = (x / (2 * (q : ℝ))) * (Real.log (2 * M / (q : ℝ) + 4) + 4) := by ring

/-- **Endgame arithmetic.**  The small-divisor and block terms (normalized so that
`K = J + 1` is the block count) are dominated by the target's second term. -/
lemma endgame (M q C K G lq T : ℝ)
    (hM : 1600 ≤ M) (hq : 4 ≤ q) (hC0 : 0 ≤ C) (hK0 : 0 ≤ K)
    (hG0 : 0 ≤ G) (hT0 : 0 ≤ T) (hlq0 : 0 ≤ lq)
    (hK : K ≤ M / (2 * q) + 3 / 4)
    (hC : C ≤ 2.7728 * T) (hG : G ≤ lq + 1.3864)
    (hpi1 : 1 / Real.pi ≤ 0.3184) (hpi2 : 2 / Real.pi ≤ 0.6367) :
    2 * q * C + (1 / Real.pi) * C * q * G + 2 * K * C + K * (2 / Real.pi) * C * q * G
      ≤ 0.89 * (M + (5 / 2) * q) * (8 + lq) * T := by
  have hq0 : 0 < q := by linarith
  have hMT : 0 ≤ M * T := mul_nonneg (by linarith) hT0
  have hqT : 0 ≤ q * T := mul_nonneg (by linarith) hT0
  have hMTlq : 0 ≤ M * T * lq := mul_nonneg hMT hlq0
  have hqTlq : 0 ≤ q * T * lq := mul_nonneg hqT hlq0
  have hqK : q * K ≤ M / 2 + 3 / 4 * q := by
    have h1 := mul_le_mul_of_nonneg_left hK (le_of_lt hq0)
    have heq : q * (M / (2 * q) + 3 / 4) = M / 2 + 3 / 4 * q := by
      field_simp
    linarith [h1, heq.le, heq.ge]
  have hMq2 : M / q ≤ M / 4 := by
    exact div_le_div_of_nonneg_left (by linarith) (by norm_num : (0 : ℝ) < 4) hq
  have h2K : 2 * K ≤ M / 4 + 3 / 2 := by
    have h2 : 2 * K ≤ 2 * (M / (2 * q) + 3 / 4) := by linarith [hK]
    have heq : 2 * (M / (2 * q) + 3 / 4) = M / q + 3 / 2 := by
      field_simp
      ring
    linarith [h2, heq.le, heq.ge, hMq2]
  have hCG : C * G ≤ (2.7728 * T) * (lq + 1.3864) :=
    mul_le_mul hC hG hG0 (by positivity)
  have h1 : 2 * q * C ≤ 5.5456 * (q * T) := by
    have h2 := mul_le_mul_of_nonneg_left hC (by linarith : (0 : ℝ) ≤ 2 * q)
    nlinarith [h2]
  have h2 : (1 / Real.pi) * C * q * G ≤ 0.8829 * (q * T * lq) + 1.2242 * (q * T) := by
    have hCG2 : C * (q * G) ≤ (2.7728 * T) * (q * (lq + 1.3864)) :=
      mul_le_mul hC (mul_le_mul_of_nonneg_left hG (by linarith))
        (mul_nonneg (by linarith) hG0) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left hCG2 (by positivity : (0 : ℝ) ≤ 1 / Real.pi)
    nlinarith [h3, hpi1, hqTlq, hqT]
  have h3 : 2 * K * C ≤ 0.6932 * (M * T) + 4.1592 * T := by
    have h2KC : 2 * K * C ≤ (M / 4 + 3 / 2) * (2.7728 * T) := by
      apply mul_le_mul h2K hC hC0 (by linarith)
    nlinarith [h2KC, hMT, hT0]
  have hpc : (2 / Real.pi) * 2.7728 ≤ 1.7655 := by nlinarith [hpi2]
  have hCG3 : (2 / Real.pi) * C * G
      ≤ (2 / Real.pi) * (2.7728 * T) * (lq + 1.3864) := by
    calc (2 / Real.pi) * C * G = (2 / Real.pi) * (C * G) := by ring
      _ ≤ (2 / Real.pi) * ((2.7728 * T) * (lq + 1.3864)) :=
          mul_le_mul_of_nonneg_left hCG (by positivity)
      _ = (2 / Real.pi) * (2.7728 * T) * (lq + 1.3864) := by ring
  have h4 : K * (2 / Real.pi) * C * q * G
      ≤ 0.88275 * (M * T * lq) + 1.22385 * (M * T)
        + 1.324125 * (q * T * lq) + 1.83577 * (q * T) := by
    have hkey : K * (2 / Real.pi) * C * q * G = (q * K) * ((2 / Real.pi) * C * G) := by
      ring
    have hstep : (q * K) * ((2 / Real.pi) * C * G)
        ≤ (M / 2 + 3 / 4 * q) * ((2 / Real.pi) * (2.7728 * T) * (lq + 1.3864)) :=
      mul_le_mul hqK hCG3 (by positivity) (by linarith)
    have hstep2 : (M / 2 + 3 / 4 * q) * ((2 / Real.pi) * (2.7728 * T) * (lq + 1.3864))
        ≤ (M / 2 + 3 / 4 * q) * 1.7655 * (T * (lq + 1.3864)) := by
      have h := mul_le_mul_of_nonneg_left hpc (by linarith : (0 : ℝ) ≤ M / 2 + 3 / 4 * q)
      calc (M / 2 + 3 / 4 * q) * ((2 / Real.pi) * (2.7728 * T) * (lq + 1.3864))
          = ((M / 2 + 3 / 4 * q) * ((2 / Real.pi) * 2.7728)) * (T * (lq + 1.3864)) := by
            ring
        _ ≤ ((M / 2 + 3 / 4 * q) * 1.7655) * (T * (lq + 1.3864)) :=
            mul_le_mul_of_nonneg_right h (by positivity)
        _ = (M / 2 + 3 / 4 * q) * 1.7655 * (T * (lq + 1.3864)) := by ring
    have hfin := le_trans hkey.le (le_trans hstep hstep2)
    nlinarith [hfin, hMT, hqT, hMTlq, hqTlq]
  nlinarith [h1, h2, h3, h4, hM, hT0]

/-! ## Stage 2: the sharp Type I assembly -/

lemma log2_le_6932 : Real.log 2 ≤ 0.6932 := by linarith [Real.log_two_lt_d9]

lemma four_log2_mul_le (T : ℝ) (hT : 0 ≤ T) : 4 * Real.log 2 * T ≤ 2.7728 * T := by
  nlinarith [log2_le_6932, hT]

lemma log_four_mul_le (q : ℝ) (hq : 1 ≤ q) : Real.log (4 * q) ≤ Real.log q + 1.3864 := by
  have hqne : q ≠ 0 := by linarith
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    rw [h]
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hqne, hlog4]
  linarith [log2_le_6932]

lemma one_div_pi_le : 1 / Real.pi ≤ 0.3184 := by
  rw [div_le_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_d4]

lemma two_div_pi_le : 2 / Real.pi ≤ 0.6367 := by
  rw [div_le_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_d4]

end TaoFivePrimesSol

theorem solution
    (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (x U V : ℝ) (hx : 0 < x) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUV : U * V ≤ x / 4)
    (W : ℕ → ℝ) (hW0 : ∀ d, 0 ≤ W d)
    (hWb : ∀ d ∈ TaoFivePrimes.theorem51Divisors U V,
        W d ≤ (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
                  (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
                else min ((1 / 2) * (x / (d : ℝ)) * Real.log x
                    + 4 * Real.log 2 * Real.log (2 * x))
                  (4 * Real.log 2 * Real.log (2 * x)
                    / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    (∑ d ∈ TaoFivePrimes.theorem51Divisors U V, W d)
      ≤ 0.5 * (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 0.89 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x) := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hqR4 : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hM1600 : 1600 ≤ U * V := by nlinarith
  have hx4 : 4 * (U * V) ≤ x := by linarith
  have hx6400 : 6400 ≤ x := by nlinarith
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hT0 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hlog2nn : 0 ≤ Real.log 2 := TaoFivePrimesAssembly.log_two_nonneg
  have hC0 : 0 ≤ 4 * Real.log 2 * Real.log (2 * x) :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hlog2nn) hT0
  set M : ℝ := U * V with hM
  set C : ℝ := 4 * Real.log 2 * Real.log (2 * x) with hC
  have hM2 : 2 * U * V / (q : ℝ) = 2 * M / (q : ℝ) := by rw [hM]; ring
  rw [hM2]
  have hM1600' : 1600 ≤ M := by rw [hM]; exact hM1600
  have hxM : 4 * M ≤ x := by rw [hM]; exact hx4
  have hC0' : 0 ≤ C := by rw [hC]; exact hC0
  set N : ℕ := ⌊M⌋₊ with hN
  have hNle : (N : ℝ) ≤ M := by
    rw [hN]
    exact Nat.floor_le (by linarith)
  have hD_eq : TaoFivePrimes.theorem51Divisors U V
      = (Finset.Icc 1 N).filter (fun d => d.Coprime 2) := rfl
  set S1 := (TaoFivePrimes.theorem51Divisors U V).filter (fun d => 2 * d ≤ q) with hS1
  set S2 := (TaoFivePrimes.theorem51Divisors U V).filter (fun d => ¬ 2 * d ≤ q) with hS2
  have hsplit : (∑ d ∈ S1, W d) + (∑ d ∈ S2, W d)
      = ∑ d ∈ TaoFivePrimes.theorem51Divisors U V, W d :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hfirst0 : 0 ≤ 0.5 * (x / (q : ℝ)) * Real.log x * (Real.log (2 * M / (q : ℝ) + 4) + 4) := by
    have h2 : 0 ≤ 0.5 * (x / (q : ℝ)) * Real.log x := by
      have : 0 ≤ x / (q : ℝ) := div_nonneg hx.le (by positivity)
      positivity
    have h1 : 0 ≤ Real.log (2 * M / (q : ℝ) + 4) + 4 := by
      have hd : 0 ≤ 2 * M / (q : ℝ) := div_nonneg (by positivity) (by positivity)
      have : (1 : ℝ) ≤ 2 * M / (q : ℝ) + 4 := by linarith
      linarith [Real.log_nonneg this]
    exact mul_nonneg h2 h1
  have hA1eq : 0.5 * (x / (q : ℝ)) * Real.log x * (Real.log (2 * M / (q : ℝ) + 4) + 4)
      = Real.log x * ((x / (2 * (q : ℝ))) * (Real.log (2 * M / (q : ℝ) + 4) + 4)) := by
    have h2q : x / (2 * (q : ℝ)) = (1 / 2) * (x / (q : ℝ)) := by field_simp
    rw [h2q]
    ring
  -- Small-divisor contribution
  have hsmall_main : (∑ d ∈ S1, W d)
      ≤ 2 * (q : ℝ) * C + (1 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
    have hwidth_small : 2 * ((((q / 2 : ℕ) : ℤ) : ℝ)) + 1 ≤ 2 * (q : ℝ) := by
      have h3 : (q / 2) * 2 ≤ q := Nat.div_mul_le_self q 2
      have h4 : (((q / 2 : ℕ)) : ℝ) * 2 ≤ (q : ℝ) := by exact_mod_cast h3
      have hbridge : ((((q / 2 : ℕ) : ℤ) : ℝ)) = ((q / 2 : ℕ) : ℝ) := by push_cast; rfl
      rw [hbridge]
      linarith
    have hv : TaoFivePrimesVinogradovSharp.oddBlockBound q (2 * (q : ℝ) * C) C (2 * alpha) 0
        (-(((q / 2 : ℕ) : ℤ) : ℝ) - 1) (((q / 2 : ℕ) : ℤ) : ℝ) := by
      intro hw
      simpa [TaoFivePrimesVinogradovSharp.vRhs] using
        TaoFivePrimes.vinogradov_odd_sharp C hC0' q hq0 (2 * (q : ℝ) * C) (2 * alpha) beta 0
          (-(((q / 2 : ℕ) : ℤ) : ℝ) - 1) (((q / 2 : ℕ) : ℤ) : ℝ) a (by positivity) haq
          (by linarith [halpha]) hbeta (by simpa using hw)
    have hpt_small : ∀ d ∈ S1,
        W d ≤ TaoFivePrimesVinogradovSharp.vmin (2 * (q : ℝ) * C) C (2 * alpha) 0 (d : ℤ) := by
      intro d hd
      rw [hS1, Finset.mem_filter] at hd
      obtain ⟨hdD, hd2q⟩ := hd
      have hdDmem : d ∈ TaoFivePrimes.theorem51Divisors U V := hdD
      rw [hD_eq, Finset.mem_filter, Finset.mem_Icc] at hdD
      obtain ⟨⟨hd1, hdN⟩, hcop⟩ := hdD
      have hd1' : 1 ≤ d := hd1
      have hd2R : (d : ℝ) * 2 ≤ (q : ℝ) := by
        have h : ((2 * d : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast hd2q
        push_cast at h
        linarith
      have hdlt : d < q := by omega
      have hkey : 4 * (d : ℝ) * alpha
          = ((a * (d : ℤ) : ℤ) : ℝ) / (q : ℝ) + (d : ℝ) * beta := by
        push_cast
        linear_combination (d : ℝ) * halpha
      have hnd : ¬ ((q : ℤ) ∣ a * (d : ℤ)) :=
        TaoFivePrimesAssembly.not_dvd_mul_of_coprime haq
          (TaoFivePrimesAssembly.not_dvd_of_lt (by omega) hdlt)
      have hrd4 := TaoFivePrimesBlock.rdist_d_alpha_ge (a * (d : ℤ)) (q : ℤ) alpha beta
        (by exact_mod_cast hq0) (by push_cast; exact hbeta) hnd d hd1' hd2R hkey
      have hqcast : (((q : ℤ)) : ℝ) = (q : ℝ) := by push_cast; rfl
      rw [hqcast] at hrd4
      have hpos4 : 0 < TaoFivePrimesBlock.rdist (4 * (d : ℝ) * alpha) :=
        lt_of_lt_of_le (by positivity) hrd4
      have hsin4ne : Real.sin (Real.pi * (4 * (d : ℝ) * alpha)) ≠ 0 :=
        TaoFivePrimesSol.sin_pi_ne_zero_of_rdist_pos hpos4
      have hsin4ge : 1 / (q : ℝ) ≤ |Real.sin (Real.pi * (4 * (d : ℝ) * alpha))| := by
        have h := TaoFivePrimesBlock.two_rdist_le_abs_sin (4 * (d : ℝ) * alpha)
        have h2 := mul_le_mul_of_nonneg_left hrd4 (by norm_num : (0 : ℝ) ≤ 2)
        have h3 : 2 * (1 / (2 * (q : ℝ))) = 1 / (q : ℝ) := by field_simp
        linarith [h2, h, h3.le, h3.ge]
      have harg4 : Real.pi * (4 * (d : ℝ) * alpha)
          = 2 * (Real.pi * (2 * alpha) * (d : ℝ)) := by ring
      have habs4 : |Real.sin (Real.pi * (4 * (d : ℝ) * alpha))|
          ≤ 2 * |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| := by
        rw [harg4, Real.sin_two_mul, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [Real.abs_cos_le_one (Real.pi * (2 * alpha) * (d : ℝ)),
          abs_nonneg (Real.sin (Real.pi * (2 * alpha) * (d : ℝ)))]
      have hsin2ge : 1 / (2 * (q : ℝ)) ≤ |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| := by
        have hh : 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) / 2 := by
          rw [div_div, mul_comm 2 (q : ℝ)]
        have h1 := div_le_div_of_nonneg_right hsin4ge (by norm_num : (0 : ℝ) ≤ 2)
        have h2 := div_le_div_of_nonneg_right habs4 (by norm_num : (0 : ℝ) ≤ 2)
        calc 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) / 2 := hh
          _ ≤ |Real.sin (Real.pi * (4 * (d : ℝ) * alpha))| / 2 := h1
          _ ≤ (2 * |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|) / 2 := h2
          _ = |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| := by ring
      have hsin2ne : Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) ≠ 0 :=
        abs_pos.mp (lt_of_lt_of_le (by positivity) hsin2ge)
      have hcosec : C / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| ≤ 2 * (q : ℝ) * C := by
        have hs : 0 < |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| :=
          lt_of_lt_of_le (by positivity) hsin2ge
        rw [div_le_iff₀ hs]
        have hmul : (1 / (2 * (q : ℝ))) * (2 * (q : ℝ) * C)
            ≤ |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| * (2 * (q : ℝ) * C) :=
          mul_le_mul_of_nonneg_right hsin2ge (by positivity)
        have hL : (1 / (2 * (q : ℝ))) * (2 * (q : ℝ) * C) = C := by field_simp
        have hR : |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| * (2 * (q : ℝ) * C)
            = 2 * (q : ℝ) * C * |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| := by ring
        linarith [hmul, hL.le, hL.ge, hR.le, hR.ge]
      have hW := hWb d hdDmem
      rw [if_neg hsin2ne] at hW
      have hWle : W d ≤ C / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| :=
        hW.trans (min_le_right _ _)
      have hle : W d ≤ TaoFivePrimesVinogradovSharp.vmin (2 * (q : ℝ) * C) C (2 * alpha) 0 (d : ℤ) := by
        unfold TaoFivePrimesVinogradovSharp.vmin
        push_cast
        rw [if_neg (by simpa using hsin2ne)]
        exact le_min (hWle.trans hcosec) (by simpa using hWle)
      exact hle
    have hSsub : S1.image (fun d : ℕ => (d : ℤ))
        ⊆ (Finset.Icc (1 : ℤ) (((q / 2 : ℕ) : ℤ))).filter (fun z => Odd z) := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨d, hd, rfl⟩ := hz
      rw [hS1, Finset.mem_filter] at hd
      obtain ⟨hdD, hd2q⟩ := hd
      rw [hD_eq, Finset.mem_filter, Finset.mem_Icc] at hdD
      obtain ⟨⟨hd1, hdN⟩, hcop⟩ := hdD
      rw [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · constructor
        · exact_mod_cast hd1
        · have h3 : d ≤ q / 2 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
          exact_mod_cast h3
      · exact (TaoFivePrimesVinogradovSharp.nat_odd_iff_int_odd d).mpr
          (Nat.coprime_two_right.mp hcop)
    calc (∑ d ∈ S1, W d)
        ≤ ∑ d ∈ S1, TaoFivePrimesVinogradovSharp.vmin (2 * (q : ℝ) * C) C (2 * alpha) 0 (d : ℤ) :=
          Finset.sum_le_sum hpt_small
      _ = ∑ z ∈ S1.image (fun d : ℕ => (d : ℤ)),
            TaoFivePrimesVinogradovSharp.vmin (2 * (q : ℝ) * C) C (2 * alpha) 0 z :=
          (Finset.sum_image (fun x _ y _ hxy => by exact_mod_cast hxy)).symm
      _ ≤ ∑ z ∈ (Finset.Icc (1 : ℤ) (((q / 2 : ℕ) : ℤ))).filter (fun z => Odd z),
            TaoFivePrimesVinogradovSharp.vmin (2 * (q : ℝ) * C) C (2 * alpha) 0 z := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hSsub
          intro z _ _
          exact TaoFivePrimesVinogradovSharp.vmin_nonneg (by positivity) hC0' z
      _ ≤ 2 * (q : ℝ) * C + (1 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ)) :=
          TaoFivePrimesVinogradovSharp.odd_symm_min_sum_le q (2 * (q : ℝ) * C) C (2 * alpha)
            (((q / 2 : ℕ) : ℤ)) hwidth_small hv
  by_cases hcase : 2 * N ≤ q
  · -- Case A: every divisor is small
    have hempty : S2 = ∅ := by
      rw [hS2, Finset.filter_eq_empty_iff]
      intro d hd hdnot
      rw [hD_eq, Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, hdN⟩, hcop⟩ := hd
      exact hdnot (by omega)
    have hsplitA : (∑ d ∈ S1, W d) = ∑ d ∈ TaoFivePrimes.theorem51Divisors U V, W d := by
      have h := hsplit
      rw [hempty, Finset.sum_empty, add_zero] at h
      exact h
    have hEndA := TaoFivePrimesSol.endgame M (q : ℝ) C 0 (Real.log (4 * (q : ℝ))) (Real.log q) (Real.log (2 * x))
      hM1600' hqR4 hC0' (le_refl 0)
      (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * (q : ℝ))) hT0 (Real.log_nonneg hq1)
      (by have h1 : 0 ≤ M / (2 * (q : ℝ)) := div_nonneg (by linarith) (by positivity); linarith)
      (TaoFivePrimesSol.four_log2_mul_le _ hT0) (TaoFivePrimesSol.log_four_mul_le _ hq1)
      TaoFivePrimesSol.one_div_pi_le TaoFivePrimesSol.two_div_pi_le
    simp only [mul_zero, zero_mul, add_zero] at hEndA
    rw [← hsplitA]
    nlinarith [hsmall_main, hEndA, hfirst0]
  · -- Case B: some divisors are large; the block decomposition takes over
    have hltN : q < 2 * N := Nat.lt_of_not_le hcase
    set J : ℕ := (2 * N - q - 1) / (4 * q) with hJ
    have hq1le : q + 1 ≤ 2 * N := by omega
    have hJle : (J : ℝ) ≤ (2 * M - (q : ℝ) - 1) / (4 * (q : ℝ)) := by
      have hsub : 2 * N - q - 1 = 2 * N - (q + 1) := by omega
      rw [hJ, hsub]
      have hnum : ((2 * N - (q + 1) : ℕ) : ℝ) ≤ 2 * M - (q : ℝ) - 1 := by
        have h2N : (2 : ℝ) * N ≤ 2 * M := by
          have := hNle
          linarith
        rw [Nat.cast_sub hq1le]
        push_cast
        linarith
      calc (((2 * N - (q + 1)) / (4 * q) : ℕ) : ℝ)
          ≤ ((2 * N - (q + 1) : ℕ) : ℝ) / ((4 * q : ℕ) : ℝ) := Nat.cast_div_le
        _ ≤ (2 * M - (q : ℝ) - 1) / (4 * (q : ℝ)) := by
            have hden2 : ((4 * q : ℕ) : ℝ) = 4 * (q : ℝ) := by push_cast; ring
            rw [hden2]
            exact div_le_div_of_nonneg_right hnum (by positivity)
    have hJ4 : 4 * (J : ℝ) ≤ 2 * M / (q : ℝ) := by
      have heq : 4 * ((2 * M - (q : ℝ) - 1) / (4 * (q : ℝ)))
          = (2 * M - (q : ℝ) - 1) / (q : ℝ) := by field_simp
      have hle : (2 * M - (q : ℝ) - 1) / (q : ℝ) ≤ 2 * M / (q : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      have h4le : 4 * (J : ℝ) ≤ 4 * ((2 * M - (q : ℝ) - 1) / (4 * (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hJle (by norm_num)
      linarith [h4le, heq.le, heq.ge, hle]
    set K : ℝ := ((J + 1 : ℕ) : ℝ) with hKdef
    have hK0 : 0 ≤ K := by rw [hKdef]; positivity
    have hKbound : K ≤ M / (2 * (q : ℝ)) + 3 / 4 := by
      have hKle : K ≤ (2 * M - (q : ℝ) - 1) / (4 * (q : ℝ)) + 1 := by
        have hK1 : K = (J : ℝ) + 1 := by rw [hKdef]; push_cast; ring
        linarith [hJle, hK1.le, hK1.ge]
      have h3 : (2 * M - (q : ℝ) - 1) / (4 * (q : ℝ)) + 1
          ≤ M / (2 * (q : ℝ)) + 3 / 4 := by
        have heq : (2 * M - (q : ℝ) - 1) / (4 * (q : ℝ)) + 1
            = M / (2 * (q : ℝ)) + 3 / 4 - 1 / (4 * (q : ℝ)) := by
          field_simp
          ring
        have hpos : 0 < 1 / (4 * (q : ℝ)) := by positivity
        linarith [heq.le, heq.ge, hpos]
      linarith [hKle, h3]
    have hcover : ∀ d, d ∈ S2 →
        d ∈ (Finset.range (J + 1)).biUnion (fun j => TaoFivePrimesAssembly.blockFinset q j) := by
      intro d hd
      rw [hS2, Finset.mem_filter] at hd
      obtain ⟨hdD, hdnot⟩ := hd
      rw [hD_eq, Finset.mem_filter, Finset.mem_Icc] at hdD
      obtain ⟨⟨hd1, hdN⟩, hcop⟩ := hdD
      have hlt : q < 2 * d := by omega
      rw [TaoFivePrimesAssembly.biUnion_blockFinset, Finset.mem_Ioc]
      constructor
      · omega
      · rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        have hltmul : 2 * N - q - 1 < (J + 1) * (4 * q) := by
          have h := TaoFivePrimesAssembly.lt_div_add_one_mul (2 * N - q - 1) (4 * q) (by omega)
          rwa [← hJ] at h
        have h2N : 2 * N ≤ 4 * J * q + 5 * q := by
          have h' : 2 * N - q - 1 < 4 * J * q + 4 * q := by
            calc 2 * N - q - 1 < (J + 1) * (4 * q) := hltmul
              _ = 4 * J * q + 4 * q := by ring
          omega
        have hX2 : 4 * (J + 1) * q + q = 4 * J * q + 5 * q := by ring
        rw [hX2]
        omega
    set Ab : ℕ → ℝ := fun j => x / (2 * TaoFivePrimesBlock.blockLeft q j) * Real.log x + C with hAb
    have hdisj : (↑(Finset.range (J + 1)) : Set ℕ).PairwiseDisjoint
        (fun j => TaoFivePrimesAssembly.blockFinset q j) := by
      intro j _ j' _ hne
      exact TaoFivePrimesAssembly.blockFinset_disjoint q j j' hne
    have hpart : (∑ d ∈ S2, W d)
        = ∑ j ∈ Finset.range (J + 1),
            ∑ d ∈ TaoFivePrimesAssembly.blockFinset q j, (if d ∈ S2 then W d else 0) := by
      have hset : ((Finset.range (J + 1)).biUnion
            (fun j => TaoFivePrimesAssembly.blockFinset q j)).filter (fun d => d ∈ S2) = S2 := by
        ext d
        rw [Finset.mem_filter]
        exact ⟨fun hd => hd.2, fun hd => ⟨hcover d hd, hd⟩⟩
      conv_lhs => rw [← hset]
      rw [Finset.sum_filter]
      exact Finset.sum_biUnion (s := Finset.range (J + 1))
        (t := fun j => TaoFivePrimesAssembly.blockFinset q j)
        (f := fun d => (if d ∈ S2 then W d else 0)) hdisj
    have hblock : ∀ j ∈ Finset.range (J + 1),
        (∑ d ∈ TaoFivePrimesAssembly.blockFinset q j, (if d ∈ S2 then W d else 0))
          ≤ 2 * Ab j + (2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
      intro j hj
      rw [← Finset.sum_filter]
      have hAj0 : 0 ≤ Ab j := by
        rw [hAb]
        have hbl : 0 < TaoFivePrimesBlock.blockLeft q j := TaoFivePrimesBlock.blockLeft_pos hq0 j
        have h1 : 0 ≤ x / (2 * TaoFivePrimesBlock.blockLeft q j) * Real.log x :=
          mul_nonneg (div_nonneg hx.le (by linarith)) hlx0
        linarith [h1, hC0']
      have hpt : ∀ d ∈ (TaoFivePrimesAssembly.blockFinset q j).filter (fun d => d ∈ S2),
          W d ≤ TaoFivePrimesVinogradovSharp.vmin (Ab j) C (2 * alpha) 0 (d : ℤ) := by
        intro d hd
        rw [Finset.mem_filter] at hd
        obtain ⟨hdblk, hdS2⟩ := hd
        rw [hS2, Finset.mem_filter] at hdS2
        obtain ⟨hdD, hdnot⟩ := hdS2
        have hdDmem : d ∈ TaoFivePrimes.theorem51Divisors U V := hdD
        rw [hD_eq, Finset.mem_filter, Finset.mem_Icc] at hdD
        obtain ⟨⟨hd1, hdN⟩, hcop⟩ := hdD
        have hblk := (TaoFivePrimesBlock.mem_block_iff q d j).mp
          ((TaoFivePrimesAssembly.mem_blockFinset_iff q j d).mp hdblk)
        have hleft : TaoFivePrimesBlock.blockLeft q j < (d : ℝ) := hblk.1
        have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
        have hW := hWb d hdDmem
        by_cases hsin : Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0
        · rw [if_pos hsin] at hW
          have hfreeze := TaoFivePrimesBlock.freeze_x_div hx hlx0 hq0 hleft hdpos
          rw [← hC] at hfreeze
          have hle : W d ≤ Ab j := by
            rw [hAb]
            linarith [hW, hfreeze]
          unfold TaoFivePrimesVinogradovSharp.vmin
          push_cast
          rw [if_pos (by simpa using hsin)]
          exact hle
        · rw [if_neg hsin] at hW
          have hfreeze := TaoFivePrimesBlock.freeze_x_div hx hlx0 hq0 hleft hdpos
          rw [← hC] at hfreeze
          have h1 : W d ≤ Ab j := by
            rw [hAb]
            have hmid := hW.trans (min_le_left _ _)
            linarith [hmid, hfreeze]
          have h2 : W d ≤ C / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))| :=
            hW.trans (min_le_right _ _)
          unfold TaoFivePrimesVinogradovSharp.vmin
          push_cast
          rw [if_neg (by simpa using hsin)]
          exact le_min h1 (by simpa using h2)
      have himg : ((TaoFivePrimesAssembly.blockFinset q j).filter (fun d => d ∈ S2)).image
            (fun d : ℕ => (d : ℤ))
          ⊆ (TaoFivePrimesVinogradovSharp.zIoc (TaoFivePrimesBlock.blockLeft q j)
              (TaoFivePrimesBlock.blockRight q j)).filter (fun z => Odd z) := by
        intro z hz
        rw [Finset.mem_image] at hz
        obtain ⟨d, hd, rfl⟩ := hz
        rw [Finset.mem_filter] at hd
        obtain ⟨hdblk, hdS2⟩ := hd
        rw [hS2, Finset.mem_filter] at hdS2
        obtain ⟨hdD, hdnot⟩ := hdS2
        rw [hD_eq, Finset.mem_filter, Finset.mem_Icc] at hdD
        obtain ⟨⟨hd1, hdN⟩, hcop⟩ := hdD
        have hblk := (TaoFivePrimesBlock.mem_block_iff q d j).mp
          ((TaoFivePrimesAssembly.mem_blockFinset_iff q j d).mp hdblk)
        rw [Finset.mem_filter, TaoFivePrimesVinogradovSharp.mem_zIoc]
        exact ⟨⟨by push_cast; exact hblk.1, by push_cast; exact hblk.2⟩,
          (TaoFivePrimesVinogradovSharp.nat_odd_iff_int_odd d).mpr
            (Nat.coprime_two_right.mp hcop)⟩
      have hw : TaoFivePrimesBlock.blockRight q j
          ≤ TaoFivePrimesBlock.blockLeft q j + 2 * (q : ℝ) := by
        have h := TaoFivePrimesBlock.blockRight_sub_blockLeft q j
        linarith
      calc (∑ d ∈ (TaoFivePrimesAssembly.blockFinset q j).filter (fun d => d ∈ S2), W d)
          ≤ ∑ d ∈ (TaoFivePrimesAssembly.blockFinset q j).filter (fun d => d ∈ S2),
              TaoFivePrimesVinogradovSharp.vmin (Ab j) C (2 * alpha) 0 (d : ℤ) :=
            Finset.sum_le_sum hpt
        _ = ∑ z ∈ ((TaoFivePrimesAssembly.blockFinset q j).filter (fun d => d ∈ S2)).image
                (fun d : ℕ => (d : ℤ)),
              TaoFivePrimesVinogradovSharp.vmin (Ab j) C (2 * alpha) 0 z :=
            (Finset.sum_image (fun x _ y _ hxy => by exact_mod_cast hxy)).symm
        _ ≤ ∑ z ∈ (TaoFivePrimesVinogradovSharp.zIoc (TaoFivePrimesBlock.blockLeft q j)
                (TaoFivePrimesBlock.blockRight q j)).filter (fun z => Odd z),
              TaoFivePrimesVinogradovSharp.vmin (Ab j) C (2 * alpha) 0 z := by
            apply Finset.sum_le_sum_of_subset_of_nonneg himg
            intro z _ _
            exact TaoFivePrimesVinogradovSharp.vmin_nonneg hAj0 hC0' z
        _ ≤ 2 * Ab j + (2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ)) :=
            TaoFivePrimes.vinogradov_odd_sharp C hC0' q hq0 (Ab j) (2 * alpha) beta 0
              (TaoFivePrimesBlock.blockLeft q j) (TaoFivePrimesBlock.blockRight q j) a hAj0 haq
              (by linarith [halpha]) hbeta hw
    have hE1 : (∑ j ∈ Finset.range (J + 1),
          (2 * Ab j + (2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ))))
        = 2 * (∑ j ∈ Finset.range (J + 1), Ab j)
          + K * ((2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ))) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · exact (Finset.mul_sum (Finset.range (J + 1)) (fun j => Ab j) (2 : ℝ)).symm
      · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hKdef]
    have hE2 : (∑ j ∈ Finset.range (J + 1), Ab j)
        = Real.log x * (∑ j ∈ Finset.range (J + 1), x / (2 * TaoFivePrimesBlock.blockLeft q j))
          + K * C := by
      have hunfold : (∑ j ∈ Finset.range (J + 1), Ab j)
          = ∑ j ∈ Finset.range (J + 1),
              (x / (2 * TaoFivePrimesBlock.blockLeft q j) * Real.log x + C) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hAb]
      rw [hunfold, Finset.sum_add_distrib,
        ← Finset.sum_mul (Finset.range (J + 1))
          (fun j => x / (2 * TaoFivePrimesBlock.blockLeft q j)) (Real.log x),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, hKdef]
      ring
    have hE3 : (∑ j ∈ Finset.range (J + 1), x / (2 * TaoFivePrimesBlock.blockLeft q j))
        = (1 / 2) * (∑ j ∈ Finset.range (J + 1), x / TaoFivePrimesBlock.blockLeft q j) := by
      rw [Finset.mul_sum (Finset.range (J + 1))
        (fun j => x / TaoFivePrimesBlock.blockLeft q j) (1 / 2)]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hsum2eq : (∑ j ∈ Finset.range (J + 1),
          (2 * Ab j + (2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ))))
        = Real.log x * (∑ j ∈ Finset.range (J + 1), x / TaoFivePrimesBlock.blockLeft q j)
          + 2 * K * C + K * ((2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ))) := by
      rw [hE1, hE2, hE3]
      ring
    have hsum_le := TaoFivePrimesSol.blocksum_le x q M hx hq0 J hJ4
    have h2le := mul_le_mul_of_nonneg_left hsum_le hlx0
    have hblocks_final : (∑ d ∈ S2, W d)
        ≤ Real.log x * ((x / (2 * (q : ℝ))) * (Real.log (2 * M / (q : ℝ) + 4) + 4))
          + 2 * K * C + K * ((2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ))) := by
      have h1 : (∑ d ∈ S2, W d)
          ≤ ∑ j ∈ Finset.range (J + 1),
              (2 * Ab j + (2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ))) := by
        rw [hpart]
        exact Finset.sum_le_sum hblock
      calc (∑ d ∈ S2, W d)
          ≤ ∑ j ∈ Finset.range (J + 1),
              (2 * Ab j + (2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ))) := h1
        _ = Real.log x * (∑ j ∈ Finset.range (J + 1), x / TaoFivePrimesBlock.blockLeft q j)
            + 2 * K * C + K * ((2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ))) :=
            hsum2eq
        _ ≤ Real.log x * ((x / (2 * (q : ℝ))) * (Real.log (2 * M / (q : ℝ) + 4) + 4))
            + 2 * K * C + K * ((2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ))) := by
            linarith [h2le]
    have hEnd := TaoFivePrimesSol.endgame M (q : ℝ) C K (Real.log (4 * (q : ℝ))) (Real.log q) (Real.log (2 * x))
      hM1600' hqR4 hC0' hK0
      (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * (q : ℝ))) hT0 (Real.log_nonneg hq1)
      hKbound (TaoFivePrimesSol.four_log2_mul_le _ hT0) (TaoFivePrimesSol.log_four_mul_le _ hq1) TaoFivePrimesSol.one_div_pi_le TaoFivePrimesSol.two_div_pi_le
    rw [← hsplit, hA1eq]
    nlinarith [hsmall_main, hblocks_final, hEnd, hfirst0]
