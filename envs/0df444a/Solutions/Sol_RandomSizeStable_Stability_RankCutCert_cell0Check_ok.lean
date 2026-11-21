-- Prove2me | solution 1 for RandomSizeStable.Stability.RankCutCert.cell0Check_ok
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T17:30:52.895185+00:00
-- url     : https://prove2.me/submissions/12d2b348-2aed-4eef-a7fc-fea01a962b05

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert
import Definitions.Def_RandomSizeStable_Stability_RankCutCertEngine

section
/-! Soundness of the Taylor-model engine (Blueprint: every statement here is a target). -/

set_option autoImplicit false

namespace RandomSizeStable.Stability.RankCutCert.Dev

/-! ### Arithmetic of `Z` -/

/-- Integer value of a `Z`. -/
def zv (a : Z) : ℤ := (a.p : ℤ) - (a.n : ℤ)

theorem SN_posR : (0 : ℝ) < (SN : ℝ) := by norm_num [SN]

theorem zadd_p (a b : Z) : (zadd a b).p = a.p + b.p := rfl
theorem zadd_n (a b : Z) : (zadd a b).n = a.n + b.n := rfl
theorem zsub_p (a b : Z) : (zsub a b).p = a.p + b.n := rfl
theorem zsub_n (a b : Z) : (zsub a b).n = a.n + b.p := rfl
theorem zmul_p (a b : Z) : (zmul a b).p = a.p * b.p + a.n * b.n := rfl
theorem zmul_n (a b : Z) : (zmul a b).n = a.p * b.n + a.n * b.p := rfl
theorem zabs_p (a : Z) : (zabs a).p = (a.p - a.n) + (a.n - a.p) := rfl
theorem zabs_n (a : Z) : (zabs a).n = 0 := rfl
theorem zaddk_p (a : Z) (k : ℕ) : (zaddk a k).p = a.p + k := rfl
theorem zaddk_n (a : Z) (k : ℕ) : (zaddk a k).n = a.n := rfl
theorem zdiv_p (a : Z) (d : ℕ) : (zdiv a d).p = (a.p - a.n) / d := rfl
theorem zdiv_n (a : Z) (d : ℕ) : (zdiv a d).n = ((a.n - a.p) + (d - 1)) / d := rfl

theorem toR_eq (a : Z) : toR a = (zv a : ℝ) / (SN : ℝ) := by
  unfold toR zv; push_cast; ring

theorem toR_zadd (a b : Z) : toR (zadd a b) = toR a + toR b := by
  unfold toR; rw [zadd_p, zadd_n]; push_cast; ring

theorem toR_zsub (a b : Z) : toR (zsub a b) = toR a - toR b := by
  unfold toR; rw [zsub_p, zsub_n]; push_cast; ring

theorem toR_zmul (a b : Z) : toR (zmul a b) = toR a * toR b * (SN : ℝ) := by
  have := SN_posR.ne'
  unfold toR; rw [zmul_p, zmul_n]; push_cast; field_simp; ring

theorem toR_zabs (a : Z) : toR (zabs a) = |toR a| := by
  unfold toR
  rw [zabs_p, zabs_n, abs_div, abs_of_pos SN_posR]
  congr 1
  rcases le_total a.p a.n with h | h
  · have hR : (a.p : ℝ) ≤ a.n := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, abs_of_nonpos (by linarith)]
    push_cast [Nat.cast_sub h]; ring
  · have hR : (a.n : ℝ) ≤ a.p := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, abs_of_nonneg (by linarith)]
    push_cast [Nat.cast_sub h]; ring

theorem toR_zaddk (a : Z) (k : ℕ) : toR (zaddk a k) = toR a + (k : ℝ) / (SN : ℝ) := by
  unfold toR; rw [zaddk_p, zaddk_n]; push_cast; ring

theorem toR_zero : toR zero = 0 := by simp [toR, zero]

theorem toR_S : toR S = 1 := by
  unfold toR S SN; norm_num

theorem toR_one : toR ⟨1, 0⟩ = 1 / (SN : ℝ) := by simp [toR]

theorem zle_iff (a b : Z) : zle a b = true ↔ toR a ≤ toR b := by
  show Nat.ble (a.p + b.n) (b.p + a.n) = true ↔ _
  rw [Nat.ble_eq]
  unfold toR
  rw [div_le_div_iff_of_pos_right SN_posR]
  constructor
  · intro h
    have := (Nat.cast_le (α := ℝ)).2 h
    push_cast at this; linarith
  · intro h
    have : ((a.p + b.n : ℕ) : ℝ) ≤ ((b.p + a.n : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

theorem zlt_iff (a b : Z) : zlt a b = true ↔ toR a < toR b := by
  show Nat.blt (a.p + b.n) (b.p + a.n) = true ↔ _
  rw [Nat.blt_eq]
  unfold toR
  rw [div_lt_div_iff_of_pos_right SN_posR]
  constructor
  · intro h
    have := (Nat.cast_lt (α := ℝ)).2 h
    push_cast at this; linarith
  · intro h
    have : ((a.p + b.n : ℕ) : ℝ) < ((b.p + a.n : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-- `zdiv` is floor division for `d > 0`. -/
theorem zdiv_spec (a : Z) (d : ℕ) (hd : 0 < d) :
    zv (zdiv a d) * d ≤ zv a ∧ zv a < (zv (zdiv a d) + 1) * d := by
  unfold zv
  rw [zdiv_p, zdiv_n]
  have hd1 : 1 ≤ d := hd
  have hdZ : (1 : ℤ) ≤ d := by exact_mod_cast hd1
  rcases le_total a.n a.p with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.div_eq_of_lt (show d - 1 < d by omega)]
    have h1 := Nat.div_add_mod (a.p - a.n) d
    have h2 := Nat.mod_lt (a.p - a.n) hd
    generalize (a.p - a.n) / d = q at h1 ⊢
    generalize (a.p - a.n) % d = r at h1 h2
    have h1' : (d : ℤ) * q + r = a.p - a.n := by
      have := congrArg (fun t : ℕ => (t : ℤ)) h1
      push_cast [Nat.cast_sub h] at this; linarith
    have h2' : (r : ℤ) < d := by exact_mod_cast h2
    have h3 : (0 : ℤ) ≤ r := by positivity
    push_cast
    constructor <;> nlinarith
  · rw [Nat.sub_eq_zero_of_le h, Nat.zero_div]
    have h1 := Nat.div_add_mod (a.n - a.p + (d - 1)) d
    have h2 := Nat.mod_lt (a.n - a.p + (d - 1)) hd
    generalize (a.n - a.p + (d - 1)) / d = q at h1 ⊢
    generalize (a.n - a.p + (d - 1)) % d = r at h1 h2
    have h1' : (d : ℤ) * q + r = a.n - a.p + d - 1 := by
      have := congrArg (fun t : ℕ => (t : ℤ)) h1
      push_cast [Nat.cast_sub h, Nat.cast_sub hd1] at this; linarith
    have h2' : (r : ℤ) < d := by exact_mod_cast h2
    have h3 : (0 : ℤ) ≤ r := by positivity
    push_cast
    constructor <;> nlinarith

theorem zq_eq (a : Z) : zq a = zdiv a SN := by
  unfold zq zq' zdiv
  congr 1
  · exact Nat.shiftRight_eq_div_pow _ _
  · exact Nat.shiftRight_eq_div_pow _ _

theorem SN_pos : 0 < SN := by norm_num [SN]

/-- `toR a / d ≤ toR (zdiv a d + 1)`. -/
theorem zdiv_le (a : Z) (d : ℕ) (hd : 0 < d) : toR a / (d : ℝ) ≤ toR (zaddk (zdiv a d) 1) := by
  obtain ⟨_, h2⟩ := zdiv_spec a d hd
  have hR : (zv a : ℝ) < ((zv (zdiv a d) : ℝ) + 1) * (d : ℝ) := by exact_mod_cast h2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hS := SN_posR
  rw [toR_zaddk, toR_eq, toR_eq, div_div, div_le_iff₀ (mul_pos hS hdR)]
  have e : ((zv (zdiv a d) : ℝ) / SN + ((1 : ℕ) : ℝ) / SN) * (SN * d) =
      ((zv (zdiv a d) : ℝ) + 1) * d := by
    field_simp; push_cast; ring
  rw [e]; exact hR.le

/-- Rounding error of `zdiv`. -/
theorem zdiv_round (a : Z) (d : ℕ) (hd : 0 < d) :
    |toR (zdiv a d) - toR a / (d : ℝ)| ≤ 1 / (SN : ℝ) := by
  obtain ⟨h1, h2⟩ := zdiv_spec a d hd
  have hR1 : (zv (zdiv a d) : ℝ) * d ≤ zv a := by exact_mod_cast h1
  have hR2 : (zv a : ℝ) < ((zv (zdiv a d) : ℝ) + 1) * (d : ℝ) := by exact_mod_cast h2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hS := SN_posR
  have e : toR (zdiv a d) - toR a / (d : ℝ) =
      ((zv (zdiv a d) : ℝ) * d - zv a) / d / SN := by
    rw [toR_eq, toR_eq]; field_simp
  rw [e, abs_div, abs_of_pos hS]
  apply div_le_div_of_nonneg_right _ hS.le
  rw [abs_div, abs_of_pos hdR, div_le_iff₀ hdR, abs_le]
  constructor <;> nlinarith

theorem zq_le (a : Z) : toR a / (SN : ℝ) ≤ toR (zaddk (zq a) 1) := by
  rw [zq_eq]; exact zdiv_le a SN SN_pos

theorem zq_round (a : Z) : |toR (zq a) - toR a / (SN : ℝ)| ≤ 1 / (SN : ℝ) := by
  rw [zq_eq]; exact zdiv_round a SN SN_pos

theorem abs3 (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le _ _).trans (by linarith [abs_add_le a b])

theorem lin_gen {B : Box} {x0 x1 x2 : ℝ} (hx : InBox B x0 x1 x2) (a0 a1 a2 K0 K1 K2 : ℝ) (N : Z)
    (h0 : |a0| ≤ K0) (h1 : |a1| ≤ K1) (h2 : |a2| ≤ K2)
    (hN : K0 * toR B.h0 + K1 * toR B.h1 + K2 * toR B.h2 = toR N / (SN : ℝ)) :
    |a0 * (x0 - toR B.m0) + a1 * (x1 - toR B.m1) + a2 * (x2 - toR B.m2)| ≤
      toR (zaddk (zq N) 1) := by
  obtain ⟨b0, b1, b2⟩ := hx
  have t0 : |a0 * (x0 - toR B.m0)| ≤ K0 * toR B.h0 := by
    rw [abs_mul]; exact mul_le_mul h0 b0 (abs_nonneg _) ((abs_nonneg _).trans h0)
  have t1 : |a1 * (x1 - toR B.m1)| ≤ K1 * toR B.h1 := by
    rw [abs_mul]; exact mul_le_mul h1 b1 (abs_nonneg _) ((abs_nonneg _).trans h1)
  have t2 : |a2 * (x2 - toR B.m2)| ≤ K2 * toR B.h2 := by
    rw [abs_mul]; exact mul_le_mul h2 b2 (abs_nonneg _) ((abs_nonneg _).trans h2)
  have := zq_le N
  linarith [abs3 (a0 * (x0 - toR B.m0)) (a1 * (x1 - toR B.m1)) (a2 * (x2 - toR B.m2))]

/-- The linear part of a model is bounded by `gsum` on the box. -/
theorem gsum_bound {B : Box} {x0 x1 x2 : ℝ} (hx : InBox B x0 x1 x2) (t : TM) :
    |toR t.g0 * (x0 - toR B.m0) + toR t.g1 * (x1 - toR B.m1) + toR t.g2 * (x2 - toR B.m2)| ≤
      toR (gsum B t) := by
  unfold gsum
  refine lin_gen hx _ _ _ _ _ _ _ le_rfl le_rfl le_rfl ?_
  have := SN_posR.ne'
  simp only [toR_zadd, toR_zmul, toR_zabs]
  field_simp

/-- Rounding slack of the linear part. -/
theorem round_lin {B : Box} {x0 x1 x2 : ℝ} (hx : InBox B x0 x1 x2) (a0 a1 a2 : ℝ)
    (h0 : |a0| ≤ 1 / (SN : ℝ)) (h1 : |a1| ≤ 1 / (SN : ℝ)) (h2 : |a2| ≤ 1 / (SN : ℝ)) :
    |a0 * (x0 - toR B.m0) + a1 * (x1 - toR B.m1) + a2 * (x2 - toR B.m2)| ≤
      toR (zaddk (zq (zadd (zadd B.h0 B.h1) B.h2)) 1) := by
  refine lin_gen hx a0 a1 a2 _ _ _ _ h0 h1 h2 ?_
  simp only [toR_zadd]; ring

theorem toR_hsum (B : Box) :
    toR (hsum B) = toR (zaddk (zq (zadd (zadd B.h0 B.h1) B.h2)) 1) + 2 / (SN : ℝ) := by
  unfold hsum; simp only [toR_zaddk]; push_cast; ring

theorem aff_eq (B : Box) (t : TM) (x0 x1 x2 : ℝ) : aff B t x0 x1 x2 = toR t.c +
    (toR t.g0 * (x0 - toR B.m0) + toR t.g1 * (x1 - toR B.m1) + toR t.g2 * (x2 - toR B.m2)) := by
  unfold aff; ring

theorem one_div_SN_nonneg : (0 : ℝ) ≤ 1 / (SN : ℝ) := by
  have := SN_posR; positivity

theorem mul_abs_le {a b A B' : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B') : |a * b| ≤ A * B' := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem valid_congr {B : Box} {f g : ℝ → ℝ → ℝ → ℝ} {t : TM} (h : Valid B f t)
    (hfg : ∀ x0 x1 x2, InBox B x0 x1 x2 → f x0 x1 x2 = g x0 x1 x2) : Valid B g t := by
  intro x0 x1 x2 hx
  rw [← hfg _ _ _ hx]
  exact h _ _ _ hx

theorem valid_add {B : Box} {f g : ℝ → ℝ → ℝ → ℝ} {x y : TM} (hx : Valid B f x) (hy : Valid B g y) :
    Valid B (fun a b c => f a b c + g a b c) (add x y) := by
  intro x0 x1 x2 hb
  have e : aff B (add x y) x0 x1 x2 = aff B x x0 x1 x2 + aff B y x0 x1 x2 := by
    simp only [add, aff, toR_zadd]; ring
  have hr : toR (add x y).r = toR x.r + toR y.r := by simp only [add, toR_zadd]
  rw [hr, e]
  have h1 := hx _ _ _ hb
  have h2 := hy _ _ _ hb
  have e2 : f x0 x1 x2 + g x0 x1 x2 - (aff B x x0 x1 x2 + aff B y x0 x1 x2) =
      (f x0 x1 x2 - aff B x x0 x1 x2) + (g x0 x1 x2 - aff B y x0 x1 x2) := by ring
  rw [e2]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem valid_sub {B : Box} {f g : ℝ → ℝ → ℝ → ℝ} {x y : TM} (hx : Valid B f x) (hy : Valid B g y) :
    Valid B (fun a b c => f a b c - g a b c) (sub x y) := by
  intro x0 x1 x2 hb
  have e : aff B (sub x y) x0 x1 x2 = aff B x x0 x1 x2 - aff B y x0 x1 x2 := by
    simp only [sub, aff, toR_zsub]; ring
  have hr : toR (sub x y).r = toR x.r + toR y.r := by simp only [sub, toR_zadd]
  rw [hr, e]
  have h1 := hx _ _ _ hb
  have h2 := hy _ _ _ hb
  have e2 : f x0 x1 x2 - g x0 x1 x2 - (aff B x x0 x1 x2 - aff B y x0 x1 x2) =
      (f x0 x1 x2 - aff B x x0 x1 x2) + -(g x0 x1 x2 - aff B y x0 x1 x2) := by ring
  rw [e2]
  exact (abs_add_le _ _).trans (add_le_add h1 (by rw [abs_neg]; exact h2))

theorem valid_mul {B : Box} {f g : ℝ → ℝ → ℝ → ℝ} {x y : TM} (hx : Valid B f x) (hy : Valid B g y) :
    Valid B (fun a b c => f a b c * g a b c) (mul B x y) := by
  intro x0 x1 x2 hb
  unfold mul mul2
  rw [aff_eq]
  dsimp only
  have hS := SN_posR
  obtain ⟨Lx, hLx⟩ : ∃ L, L = toR x.g0 * (x0 - toR B.m0) + toR x.g1 * (x1 - toR B.m1) +
      toR x.g2 * (x2 - toR B.m2) := ⟨_, rfl⟩
  obtain ⟨Ly, hLy⟩ : ∃ L, L = toR y.g0 * (x0 - toR B.m0) + toR y.g1 * (x1 - toR B.m1) +
      toR y.g2 * (x2 - toR B.m2) := ⟨_, rfl⟩
  have bLx : |Lx| ≤ toR (gsum B x) := hLx ▸ gsum_bound hb x
  have bLy : |Ly| ≤ toR (gsum B y) := hLy ▸ gsum_bound hb y
  obtain ⟨ex, hfex⟩ : ∃ e, f x0 x1 x2 = toR x.c + Lx + e := ⟨f x0 x1 x2 - (toR x.c + Lx), by ring⟩
  obtain ⟨ey, hgey⟩ : ∃ e, g x0 x1 x2 = toR y.c + Ly + e := ⟨g x0 x1 x2 - (toR y.c + Ly), by ring⟩
  have bex : |ex| ≤ toR x.r := by
    have := hx _ _ _ hb
    rw [aff_eq, ← hLx, hfex] at this
    simpa using this
  have bey : |ey| ≤ toR y.r := by
    have := hy _ _ _ hb
    rw [aff_eq, ← hLy, hgey] at this
    simpa using this
  have bu : |toR x.c + Lx| ≤ |toR x.c| + toR (gsum B x) :=
    (abs_add_le _ _).trans (by linarith)
  have bv : |toR y.c + Ly| ≤ |toR y.c| + toR (gsum B y) :=
    (abs_add_le _ _).trans (by linarith)
  -- the main (product) error
  have bE1 : |Lx * Ly + ex * (toR y.c + Ly) + ey * (toR x.c + Lx) + ex * ey| ≤
      toR (zaddk (zq (zadd (zadd (zadd (zmul (gsum B x) (gsum B y))
        (zmul (zadd (zabs x.c) (gsum B x)) y.r)) (zmul (zadd (zabs y.c) (gsum B y)) x.r))
        (zmul x.r y.r))) 1) := by
    have t1 := mul_abs_le bLx bLy
    have t2 := mul_abs_le bex bv
    have t3 := mul_abs_le bey bu
    have t4 := mul_abs_le bex bey
    have key : toR (gsum B x) * toR (gsum B y) + toR x.r * (|toR y.c| + toR (gsum B y)) +
        toR y.r * (|toR x.c| + toR (gsum B x)) + toR x.r * toR y.r =
        toR (zadd (zadd (zadd (zmul (gsum B x) (gsum B y))
          (zmul (zadd (zabs x.c) (gsum B x)) y.r)) (zmul (zadd (zabs y.c) (gsum B y)) x.r))
          (zmul x.r y.r)) / (SN : ℝ) := by
      simp only [toR_zadd, toR_zmul, toR_zabs]; field_simp; ring
    have := zq_le (zadd (zadd (zadd (zmul (gsum B x) (gsum B y))
          (zmul (zadd (zabs x.c) (gsum B x)) y.r)) (zmul (zadd (zabs y.c) (gsum B y)) x.r))
          (zmul x.r y.r))
    have a1 := abs_add_le (Lx * Ly + ex * (toR y.c + Ly) + ey * (toR x.c + Lx)) (ex * ey)
    have a2 := abs3 (Lx * Ly) (ex * (toR y.c + Ly)) (ey * (toR x.c + Lx))
    linarith
  have hround : ∀ a b c d : Z, |(toR a * toR b + toR c * toR d) -
      toR (zq (zadd (zmul a b) (zmul c d)))| ≤ 1 / (SN : ℝ) := by
    intro a b c d
    rw [abs_sub_comm]
    have := zq_round (zadd (zmul a b) (zmul c d))
    convert this using 3
    simp only [toR_zadd, toR_zmul]; field_simp
  have bc : |toR x.c * toR y.c - toR (zq (zmul x.c y.c))| ≤ 1 / (SN : ℝ) := by
    rw [abs_sub_comm]
    have := zq_round (zmul x.c y.c)
    convert this using 3
    simp only [toR_zmul]; field_simp
  have bL := round_lin hb _ _ _ (hround x.c y.g0 y.c x.g0) (hround x.c y.g1 y.c x.g1)
    (hround x.c y.g2 y.c x.g2)
  have ident : f x0 x1 x2 * g x0 x1 x2 - (toR (zq (zmul x.c y.c)) +
      (toR (zq (zadd (zmul x.c y.g0) (zmul y.c x.g0))) * (x0 - toR B.m0) +
        toR (zq (zadd (zmul x.c y.g1) (zmul y.c x.g1))) * (x1 - toR B.m1) +
        toR (zq (zadd (zmul x.c y.g2) (zmul y.c x.g2))) * (x2 - toR B.m2))) =
      (Lx * Ly + ex * (toR y.c + Ly) + ey * (toR x.c + Lx) + ex * ey) +
      (toR x.c * toR y.c - toR (zq (zmul x.c y.c))) +
      (((toR x.c * toR y.g0 + toR y.c * toR x.g0) - toR (zq (zadd (zmul x.c y.g0) (zmul y.c x.g0)))) *
          (x0 - toR B.m0) +
        ((toR x.c * toR y.g1 + toR y.c * toR x.g1) - toR (zq (zadd (zmul x.c y.g1) (zmul y.c x.g1)))) *
          (x1 - toR B.m1) +
        ((toR x.c * toR y.g2 + toR y.c * toR x.g2) - toR (zq (zadd (zmul x.c y.g2) (zmul y.c x.g2)))) *
          (x2 - toR B.m2)) := by
    rw [hfex, hgey, hLx, hLy]; ring
  rw [ident]
  have tot : toR (zadd (zq (zadd (zadd (zadd (zmul (gsum B x) (gsum B y))
        (zmul (zadd (zabs x.c) (gsum B x)) y.r)) (zmul (zadd (zabs y.c) (gsum B y)) x.r))
        (zmul x.r y.r))) (hsum B)) =
      toR (zaddk (zq (zadd (zadd (zadd (zmul (gsum B x) (gsum B y))
        (zmul (zadd (zabs x.c) (gsum B x)) y.r)) (zmul (zadd (zabs y.c) (gsum B y)) x.r))
        (zmul x.r y.r))) 1) + 1 / (SN : ℝ) + toR (zaddk (zq (zadd (zadd B.h0 B.h1) B.h2)) 1) := by
    rw [toR_zadd, toR_hsum]; simp only [toR_zaddk]; push_cast; ring
  rw [tot]
  exact (abs3 _ _ _).trans (by linarith)

theorem valid_qmul {B : Box} {f : ℝ → ℝ → ℝ → ℝ} {x : TM} (n : Z) (d : Nat) (hd : 0 < d)
    (hx : Valid B f x) :
    Valid B (fun a b c => ((n.p : ℝ) - (n.n : ℝ)) / (d : ℝ) * f a b c) (qmul B n d x) := by
  intro x0 x1 x2 hb
  unfold qmul
  rw [aff_eq]
  dsimp only
  have hS := SN_posR
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hn : ((n.p : ℝ) - (n.n : ℝ)) = toR n * (SN : ℝ) := by unfold toR; field_simp
  rw [hn]
  obtain ⟨Lx, hLx⟩ : ∃ L, L = toR x.g0 * (x0 - toR B.m0) + toR x.g1 * (x1 - toR B.m1) +
      toR x.g2 * (x2 - toR B.m2) := ⟨_, rfl⟩
  obtain ⟨ex, hfex⟩ : ∃ e, f x0 x1 x2 = toR x.c + Lx + e := ⟨f x0 x1 x2 - (toR x.c + Lx), by ring⟩
  have bex : |ex| ≤ toR x.r := by
    have := hx _ _ _ hb
    rw [aff_eq, ← hLx, hfex] at this
    simpa using this
  have hq : ∀ a : Z, |toR n * (SN : ℝ) / (d : ℝ) * toR a - toR (zdiv (zmul n a) d)| ≤
      1 / (SN : ℝ) := by
    intro a
    rw [abs_sub_comm]
    have := zdiv_round (zmul n a) d hd
    convert this using 3
    rw [toR_zmul]; ring
  have bL := round_lin hb _ _ _ (hq x.g0) (hq x.g1) (hq x.g2)
  have be : |toR n * (SN : ℝ) / (d : ℝ) * ex| ≤ toR (zaddk (zdiv (zmul (zabs n) x.r) d) 1) := by
    have h1 : |toR n * (SN : ℝ) / (d : ℝ) * ex| ≤ |toR n * (SN : ℝ) / (d : ℝ)| * toR x.r := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left bex (abs_nonneg _)
    have h2 : |toR n * (SN : ℝ) / (d : ℝ)| * toR x.r = toR (zmul (zabs n) x.r) / (d : ℝ) := by
      rw [toR_zmul, toR_zabs, abs_div, abs_mul, abs_of_pos hS, abs_of_pos hdR]; ring
    have h3 := zdiv_le (zmul (zabs n) x.r) d hd
    linarith
  have ident : toR n * (SN : ℝ) / (d : ℝ) * f x0 x1 x2 - (toR (zdiv (zmul n x.c) d) +
      (toR (zdiv (zmul n x.g0) d) * (x0 - toR B.m0) + toR (zdiv (zmul n x.g1) d) * (x1 - toR B.m1) +
        toR (zdiv (zmul n x.g2) d) * (x2 - toR B.m2))) =
      toR n * (SN : ℝ) / (d : ℝ) * ex +
      (toR n * (SN : ℝ) / (d : ℝ) * toR x.c - toR (zdiv (zmul n x.c) d)) +
      ((toR n * (SN : ℝ) / (d : ℝ) * toR x.g0 - toR (zdiv (zmul n x.g0) d)) * (x0 - toR B.m0) +
        (toR n * (SN : ℝ) / (d : ℝ) * toR x.g1 - toR (zdiv (zmul n x.g1) d)) * (x1 - toR B.m1) +
        (toR n * (SN : ℝ) / (d : ℝ) * toR x.g2 - toR (zdiv (zmul n x.g2) d)) * (x2 - toR B.m2)) := by
    rw [hfex, hLx]; ring
  rw [ident]
  have bc := hq x.c
  have tot : toR (zadd (zaddk (zdiv (zmul (zabs n) x.r) d) 1) (hsum B)) =
      toR (zaddk (zdiv (zmul (zabs n) x.r) d) 1) + 1 / (SN : ℝ) +
        toR (zaddk (zq (zadd (zadd B.h0 B.h1) B.h2)) 1) + 1 / (SN : ℝ) := by
    rw [toR_zadd, toR_hsum]; ring
  have h1pos := one_div_SN_nonneg
  rw [tot]
  exact (abs3 _ _ _).trans (by linarith)

theorem valid_cnst (B : Box) (k : Z) : Valid B (fun _ _ _ => toR k) (cnst k) := by
  intro x0 x1 x2 _
  simp [cnst, aff, toR_zero]

theorem valid_cq (B : Box) (n : Z) (d : Nat) (hd : 0 < d) :
    Valid B (fun _ _ _ => ((n.p : ℝ) - (n.n : ℝ)) / (d : ℝ)) (cq n d) := by
  intro x0 x1 x2 _
  simp only [cq, aff, toR_zero, zero_mul, add_zero, toR_one]
  rw [abs_sub_comm]
  have := zdiv_round (zmul n S) d hd
  convert this using 3
  rw [toR_zmul, toR_S]
  have := SN_posR.ne'
  unfold toR; field_simp

theorem valid_var0 (B : Box) : Valid B (fun x _ _ => x) (var0 B) := by
  intro x0 x1 x2 _
  simp only [var0, aff, toR_S, toR_zero, zero_mul, add_zero, one_mul]
  simp

theorem valid_var1 (B : Box) : Valid B (fun _ x _ => x) (var1 B) := by
  intro x0 x1 x2 _
  simp only [var1, aff, toR_S, toR_zero, zero_mul, add_zero, one_mul]
  simp

theorem valid_var2 (B : Box) : Valid B (fun _ _ x => x) (var2 B) := by
  intro x0 x1 x2 _
  simp only [var2, aff, toR_S, toR_zero, zero_mul, add_zero, one_mul]
  simp

theorem valid_constOf {k : ℝ} {t : TM} (h : Valid B0 (fun _ _ _ => k) t) (B : Box) :
    Valid B (fun _ _ _ => k) (constOf t) := by
  have h0 := h 0 0 0 (by simp [InBox, B0, toR_zero])
  simp only [aff, B0, toR_zero, sub_zero, mul_zero, add_zero] at h0
  intro x0 x1 x2 _
  simpa only [constOf, aff, toR_zero, zero_mul, add_zero] using h0

theorem lower_le {B : Box} {f : ℝ → ℝ → ℝ → ℝ} {t : TM} (h : Valid B f t) {x0 x1 x2 : ℝ}
    (hx : InBox B x0 x1 x2) : toR (lower B t) ≤ f x0 x1 x2 := by
  have h1 := h _ _ _ hx
  have h2 := gsum_bound hx t
  rw [aff_eq] at h1
  unfold lower
  rw [toR_zsub, toR_zsub]
  rw [abs_le] at h1 h2
  linarith [h1.1, h2.1]

theorem le_upper {B : Box} {f : ℝ → ℝ → ℝ → ℝ} {t : TM} (h : Valid B f t) {x0 x1 x2 : ℝ}
    (hx : InBox B x0 x1 x2) : f x0 x1 x2 ≤ toR (upper B t) := by
  have h1 := h _ _ _ hx
  have h2 := gsum_bound hx t
  rw [aff_eq] at h1
  unfold upper
  rw [toR_zadd, toR_zadd]
  rw [abs_le] at h1 h2
  linarith [h1.2, h2.2]

theorem sqS_step (u : Z) {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ toR u) : y ^ 2 ≤ toR (sqS u) := by
  have h1 : y ^ 2 ≤ toR u ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have h2 : toR u ^ 2 = toR (zmul u u) / (SN : ℝ) := by
    have := SN_posR.ne'
    rw [toR_zmul]; field_simp
  have h3 := zq_le (zmul u u)
  unfold sqS
  linarith

theorem upow32_bound (u : Z) {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ toR u) :
    y ^ 32 ≤ toR (upow32 u) := by
  unfold upow32
  have e : y ^ 32 = ((((y ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by ring
  rw [e]
  apply sqS_step _ (by positivity)
  apply sqS_step _ (by positivity)
  apply sqS_step _ (by positivity)
  apply sqS_step _ (by positivity)
  exact sqS_step _ hy0 hy

theorem valid_pow32 {B : Box} {f : ℝ → ℝ → ℝ → ℝ} {x x2 : TM} (hx : Valid B f x)
    (hx2 : Valid B (fun a b c => f a b c ^ 2) x2) :
    Valid B (fun a b c => f a b c ^ 32) (pow32 B x x2) := by
  unfold pow32 pow32a
  cases hc : (zle zero (lower B x) && zle (upow32 (upper B x)) ⟨17179869184, 0⟩)
  · have h4 : Valid B (fun a b c => f a b c ^ 4) (sqT B x2) :=
      valid_congr (valid_mul hx2 hx2) (fun a b c _ => by ring)
    have h8 : Valid B (fun a b c => f a b c ^ 8) (sqT B (sqT B x2)) :=
      valid_congr (valid_mul h4 h4) (fun a b c _ => by ring)
    have h16 : Valid B (fun a b c => f a b c ^ 16) (sqT B (sqT B (sqT B x2))) :=
      valid_congr (valid_mul h8 h8) (fun a b c _ => by ring)
    exact valid_congr (valid_mul h16 h16) (fun a b c _ => by ring)
  · simp only [Bool.and_eq_true, zle_iff, toR_zero] at hc
    intro x0 x1 x2 hb
    have hl := lower_le hx hb
    have hu := le_upper hx hb
    have f0 : 0 ≤ f x0 x1 x2 := le_trans hc.1 hl
    have hF := upow32_bound (upper B x) f0 hu
    have hF0 : 0 ≤ f x0 x1 x2 ^ 32 := by positivity
    have hU2 : toR (zdiv (upow32 (upper B x)) 2) ≤ toR (upow32 (upper B x)) -
        toR (zdiv (upow32 (upper B x)) 2) := by
      have := (zdiv_spec (upow32 (upper B x)) 2 (by norm_num)).1
      have hR : (zv (zdiv (upow32 (upper B x)) 2) : ℝ) * 2 ≤ zv (upow32 (upper B x)) := by
        exact_mod_cast this
      rw [toR_eq, toR_eq, div_sub_div_same, div_le_div_iff_of_pos_right SN_posR]
      linarith
    show |f x0 x1 x2 ^ 32 - aff B ⟨zdiv (upow32 (upper B x)) 2, zero, zero, zero,
      zsub (upow32 (upper B x)) (zdiv (upow32 (upper B x)) 2)⟩ x0 x1 x2| ≤
      toR (zsub (upow32 (upper B x)) (zdiv (upow32 (upper B x)) 2))
    simp only [aff, toR_zero, zero_mul, add_zero]
    rw [toR_zsub]
    rw [abs_le]
    constructor <;> linarith

/-- All five powers of `pows`. -/
def PwValid (B : Box) (f : ℝ → ℝ → ℝ → ℝ) (P : Pw) : Prop :=
  Valid B f P.x1 ∧ Valid B (fun a b c => f a b c ^ 2) P.x2 ∧ Valid B (fun a b c => f a b c ^ 3) P.x3 ∧
    Valid B (fun a b c => f a b c ^ 32) P.x32 ∧ Valid B (fun a b c => f a b c ^ 33) P.x33

theorem valid_pows {B : Box} {f : ℝ → ℝ → ℝ → ℝ} {x : TM} (hx : Valid B f x) :
    PwValid B f (pows B x) := by
  have h2 : Valid B (fun a b c => f a b c ^ 2) (mul B x x) :=
    valid_congr (valid_mul hx hx) (fun a b c _ => by ring)
  have h3 : Valid B (fun a b c => f a b c ^ 3) (mul B (mul B x x) x) :=
    valid_congr (valid_mul h2 hx) (fun a b c _ => by ring)
  have h32 := valid_pow32 hx h2
  have h33 : Valid B (fun a b c => f a b c ^ 33) (mul B (pow32 B x (mul B x x)) x) :=
    valid_congr (valid_mul h32 hx) (fun a b c _ => by ring)
  exact ⟨hx, h2, h3, h32, h33⟩

theorem valid_phiT {B : Box} {f : ℝ → ℝ → ℝ → ℝ} {P : Pw} (hP : PwValid B f P) :
    Valid B (fun a b c => phi (f a b c)) (phiT B P) := by
  obtain ⟨h1, h2, _, h32, _⟩ := hP
  have := valid_add (valid_add (valid_qmul ⟨19, 0⟩ 73 (by norm_num) h1)
    (valid_qmul ⟨35, 0⟩ 146 (by norm_num) h2)) (valid_qmul ⟨1, 0⟩ 2 (by norm_num) h32)
  refine valid_congr this (fun a b c _ => ?_)
  simp only [phi]
  push_cast
  ring

theorem valid_PhiT {B : Box} {f : ℝ → ℝ → ℝ → ℝ} {P : Pw} (hP : PwValid B f P) :
    Valid B (fun a b c => Phi (f a b c)) (PhiT B P) := by
  obtain ⟨_, h2, h3, _, h33⟩ := hP
  have := valid_add (valid_add (valid_qmul ⟨19, 0⟩ 146 (by norm_num) h2)
    (valid_qmul ⟨35, 0⟩ 438 (by norm_num) h3)) (valid_qmul ⟨1, 0⟩ 66 (by norm_num) h33)
  refine valid_congr this (fun a b c _ => ?_)
  simp only [Phi]
  push_cast
  ring

theorem half_split (m h : Z) (hh : zeven h = true) (x : ℝ) (hx : |x - toR m| ≤ toR h) :
    |x - toR (zsub m (zdiv h 2))| ≤ toR (zdiv h 2) ∨
      |x - toR (zadd m (zdiv h 2))| ≤ toR (zdiv h 2) := by
  have hm : (h.p + h.n) % 2 = 0 := Nat.eq_of_beq_eq_true hh
  obtain ⟨s1, s2⟩ := zdiv_spec h 2 (by norm_num)
  have e : zv (zdiv h 2) * 2 = zv h := by
    unfold zv at s1 s2 ⊢
    omega
  have eR : toR (zdiv h 2) * 2 = toR h := by
    rw [toR_eq, toR_eq, ← e]; push_cast; ring
  rw [toR_zsub, toR_zadd]
  rw [abs_le] at hx
  rcases le_total x (toR m) with hxm | hxm
  · left; rw [abs_le]; constructor <;> linarith
  · right; rw [abs_le]; constructor <;> linarith

/-- Points of a box split along dimension `i` lie in one of the two halves (when `h_i` is even). -/
theorem inBox_split (B : Box) (i : Nat) (he : evenH B i = true) {x0 x1 x2 : ℝ}
    (hx : InBox B x0 x1 x2) : InBox (splitL B i) x0 x1 x2 ∨ InBox (splitR B i) x0 x1 x2 := by
  obtain ⟨b0, b1, b2⟩ := hx
  rcases i with _ | _ | i
  · simp only [evenH] at he
    simp only [splitL, splitR, InBox]
    rcases half_split _ _ he _ b0 with h | h
    · exact Or.inl ⟨h, b1, b2⟩
    · exact Or.inr ⟨h, b1, b2⟩
  · simp only [evenH] at he
    simp only [splitL, splitR, InBox]
    rcases half_split _ _ he _ b1 with h | h
    · exact Or.inl ⟨b0, h, b2⟩
    · exact Or.inr ⟨b0, h, b2⟩
  · simp only [evenH] at he
    simp only [splitL, splitR, InBox]
    rcases half_split _ _ he _ b2 with h | h
    · exact Or.inl ⟨b0, b1, h⟩
    · exact Or.inr ⟨b0, b1, h⟩

theorem run_sound (leaf : Box → Bool) (Q : ℝ → ℝ → ℝ → Prop)
    (hleaf : ∀ B, leaf B = true → ∀ x0 x1 x2, InBox B x0 x1 x2 → Q x0 x1 x2) :
    ∀ (n : Nat) (B : Box) (code rest : List Nat), run leaf n B code = some rest →
      ∀ x0 x1 x2, InBox B x0 x1 x2 → Q x0 x1 x2 := by
  intro n
  induction n with
  | zero => intro B code rest h; simp [run] at h
  | succ n ih =>
    intro B code rest h x0 x1 x2 hx
    match code, h with
    | [], h => simp [run] at h
    | 0 :: c, h =>
      simp only [run] at h
      split_ifs at h with hl
      exact hleaf B hl x0 x1 x2 hx
    | (i + 1) :: c, h =>
      simp only [run] at h
      split_ifs at h with he
      cases hL : run leaf n (splitL B i) c with
      | none => rw [hL] at h; simp at h
      | some r' =>
        rw [hL] at h
        rcases inBox_split B i he hx with h1 | h1
        · exact ih _ _ _ hL _ _ _ h1
        · exact ih _ _ _ h _ _ _ h1

theorem runAll_sound (leaf : Box → Bool) (Q : ℝ → ℝ → ℝ → Prop)
    (hleaf : ∀ B, leaf B = true → ∀ x0 x1 x2, InBox B x0 x1 x2 → Q x0 x1 x2)
    (B : Box) (code : List Nat) (h : runAll leaf B code = true) :
    ∀ x0 x1 x2, InBox B x0 x1 x2 → Q x0 x1 x2 := by
  unfold runAll at h
  split at h
  · exact run_sound leaf Q hleaf 64 B code [] ‹_›
  · simp at h

end RandomSizeStable.Stability.RankCutCert.Dev
end

section
/-! Soundness of the interior-cell checker (Blueprint). -/

set_option autoImplicit false

namespace RandomSizeStable.Stability.RankCutCert.Dev

/-! ### Integer helpers -/

theorem zle_zv (a b : Z) : zle a b = true ↔ zv a ≤ zv b := by
  show Nat.ble (a.p + b.n) (b.p + a.n) = true ↔ _
  rw [Nat.ble_eq]; unfold zv; omega

theorem zlt_zv (a b : Z) : zlt a b = true ↔ zv a < zv b := by
  show Nat.blt (a.p + b.n) (b.p + a.n) = true ↔ _
  rw [Nat.blt_eq]; unfold zv; omega

theorem zv_zmul_S (a : Z) : zv (zmul a S) = zv a * (SN : ℤ) := by
  unfold zv; rw [zmul_p, zmul_n]; simp only [S, SN]; push_cast; ring

theorem zv_zneg (a : Z) : zv (zneg a) = - zv a := by
  unfold zv zneg; ring

theorem zdiv_zero' (a : Z) : zdiv a 0 = zero := by
  unfold zdiv zero; congr 1 <;> exact Nat.div_zero _

theorem qR_eq (q : Q) : qR q = (zv q.n : ℝ) / (q.d : ℝ) := by
  unfold qR zv; push_cast; ring

theorem le_toR_iff (a : Z) (y : ℝ) : toR a ≤ y ↔ (zv a : ℝ) ≤ y * SN := by
  rw [toR_eq, div_le_iff₀ SN_posR]

theorem toR_le_iff (a : Z) (y : ℝ) : y ≤ toR a ↔ y * SN ≤ (zv a : ℝ) := by
  rw [toR_eq, le_div_iff₀ SN_posR]

theorem floorS_spec (q : Q) (hd : 0 < q.d) :
    (zv (floorS q) : ℝ) ≤ qR q * SN ∧ qR q * SN < zv (floorS q) + 1 := by
  obtain ⟨h1, h2⟩ := zdiv_spec (zmul q.n S) q.d hd
  rw [zv_zmul_S] at h1 h2
  have hdR : (0 : ℝ) < q.d := by exact_mod_cast hd
  have h1' : (zv (floorS q) : ℝ) * q.d ≤ zv q.n * SN := by unfold floorS; exact_mod_cast h1
  have h2' : (zv q.n : ℝ) * SN < (zv (floorS q) + 1) * q.d := by unfold floorS; exact_mod_cast h2
  rw [qR_eq, div_mul_eq_mul_div]
  constructor
  · rw [le_div_iff₀ hdR]; linarith
  · rw [div_lt_iff₀ hdR]; linarith

theorem ceilS_spec (q : Q) (hd : 0 < q.d) :
    (zv (ceilS q) : ℝ) - 1 < qR q * SN ∧ qR q * SN ≤ zv (ceilS q) := by
  obtain ⟨h1, h2⟩ := zdiv_spec (zneg (zmul q.n S)) q.d hd
  rw [zv_zneg, zv_zmul_S] at h1 h2
  have hdR : (0 : ℝ) < q.d := by exact_mod_cast hd
  have hc : zv (ceilS q) = - zv (zdiv (zneg (zmul q.n S)) q.d) := by unfold ceilS; rw [zv_zneg]
  have h1' : (zv (zdiv (zneg (zmul q.n S)) q.d) : ℝ) * q.d ≤ -(zv q.n * SN) := by exact_mod_cast h1
  have h2' : -((zv q.n : ℝ) * SN) < (zv (zdiv (zneg (zmul q.n S)) q.d) + 1) * q.d := by
    exact_mod_cast h2
  have hcR : (zv (ceilS q) : ℝ) = - zv (zdiv (zneg (zmul q.n S)) q.d) := by exact_mod_cast hc
  rw [qR_eq, div_mul_eq_mul_div, hcR]
  constructor
  · rw [lt_div_iff₀ hdR]; linarith
  · rw [div_le_iff₀ hdR]; linarith

/-! ### Validity helpers -/

theorem hsum_nonneg {B : Box} {x0 x1 x2 : ℝ} (hx : InBox B x0 x1 x2) : 0 ≤ toR (hsum B) := by
  rw [toR_hsum]
  have := zq_le (zadd (zadd B.h0 B.h1) B.h2)
  simp only [toR_zadd] at this
  obtain ⟨b0, b1, b2⟩ := hx
  have := abs_nonneg (x0 - toR B.m0); have := abs_nonneg (x1 - toR B.m1)
  have := abs_nonneg (x2 - toR B.m2)
  have : 0 ≤ (toR B.h0 + toR B.h1 + toR B.h2) / (SN : ℝ) := div_nonneg (by linarith) SN_posR.le
  have : (0 : ℝ) ≤ 2 / (SN : ℝ) := div_nonneg (by norm_num) SN_posR.le
  linarith


theorem valid_qm (B : Box) (q : Q) {f : ℝ → ℝ → ℝ → ℝ} {x : TM} (hx : Valid B f x) :
    Valid B (fun a b c => qR q * f a b c) (qm B q x) := by
  rcases Nat.eq_zero_or_pos q.d with hd | hd
  · intro x0 x1 x2 hb
    have hq : qR q = 0 := by simp [qR, hd]
    have hs := hsum_nonneg hb
    have h1 : (0 : ℝ) ≤ 1 / (SN : ℝ) := one_div_SN_nonneg
    simp only [qm, qmul, hd, zdiv_zero', aff, hq, zero_mul, toR_zero, toR_zadd, toR_zaddk]
    simp only [sub_zero, add_zero, abs_zero, Nat.cast_one]
    linarith
  · exact valid_qmul q.n q.d hd hx

theorem valid_cqQ (B : Box) (q : Q) : Valid B (fun _ _ _ => qR q) (cqQ q) := by
  rcases Nat.eq_zero_or_pos q.d with hd | hd
  · intro x0 x1 x2 hb
    have hq : qR q = 0 := by simp [qR, hd]
    have h1 : (0 : ℝ) ≤ 1 / (SN : ℝ) := one_div_SN_nonneg
    simp only [cqQ, cq, hd, zdiv_zero', aff, hq, zero_mul, toR_zero, toR_one]
    simp only [sub_zero, add_zero, abs_zero]
    exact h1
  · exact valid_cq B q.n q.d hd

theorem valid_one (B : Box) : Valid B (fun _ _ _ => (1 : ℝ)) (cnst S) := by
  have := valid_cnst B S
  simp only [toR_S] at this
  exact this

theorem valid_zeroT (B : Box) : Valid B (fun _ _ _ => (0 : ℝ)) (cnst zero) := by
  have := valid_cnst B zero
  simp only [toR_zero] at this
  exact this

/-! ### The witness constants -/

theorem qR_etaQ (j : Fin 9) : qR (etaQ j) = eta j := by
  fin_cases j <;> norm_num [qR, etaQ, eta]

theorem qR_hQ (j : Fin 9) : qR (hQ j) = h j := by
  fin_cases j <;> norm_num [qR, hQ, h]

theorem qR_loQ (j : Fin 9) : qR (loQ j) = lo j := by
  fin_cases j <;> norm_num [qR, loQ, lo]

theorem qR_hiQ (j : Fin 9) : qR (hiQ j) = hi j := by
  fin_cases j <;> norm_num [qR, hiQ, hi]

theorem qR_bQ : qR bQ = b := by norm_num [qR, bQ, b]
theorem qR_C0Q : qR C0Q = C0 := by norm_num [qR, C0Q, C0]
theorem qR_muQ : qR muQ = mu := by norm_num [qR, muQ, mu]

theorem d_hQ (j : Fin 9) : 0 < (hQ j).d := by fin_cases j <;> simp [hQ]
theorem d_loQ (j : Fin 9) : 0 < (loQ j).d := by fin_cases j <;> simp [loQ]
theorem d_hiQ (j : Fin 9) : 0 < (hiQ j).d := by fin_cases j <;> simp [hiQ]
theorem d_bQ : 0 < bQ.d := by simp [bQ]

theorem valid_phiConst (q : Q) : Valid B0 (fun _ _ _ => phi (qR q)) (phiConst q) :=
  valid_phiT (valid_pows (valid_cqQ B0 q))

theorem valid_ktT (j : Fin 9) (B : Box) :
    Valid B (fun _ _ _ => eta j * phi (h j) - h j) (ktT j) :=
  valid_constOf (valid_congr (valid_sub (valid_qm B0 (etaQ j) (valid_phiConst (hQ j)))
    (valid_cqQ B0 (hQ j))) (fun _ _ _ _ => by simp only [qR_etaQ, qR_hQ])) B

theorem valid_psiLoT (j : Fin 9) (B : Box) :
    Valid B (fun _ _ _ => mu - phi (lo j)) (psiLoT j) :=
  valid_constOf (valid_congr (valid_sub (valid_cqQ B0 muQ) (valid_phiConst (loQ j)))
    (fun _ _ _ _ => by simp only [qR_muQ, qR_loQ])) B

theorem valid_psiBT (B : Box) : Valid B (fun _ _ _ => mu - phi b) psiBT :=
  valid_constOf (valid_congr (valid_sub (valid_cqQ B0 muQ) (valid_phiConst bQ))
    (fun _ _ _ _ => by simp only [qR_muQ, qR_bQ])) B


/-! ### Pieces of `tail` and `mu - phi ∘ rho` -/

noncomputable def tailR (j : Fin 9) (y : ℝ) : Nat → ℝ
  | 0 => C0
  | 1 => (eta j * phi (h j) - h j) + y - eta j * phi y
  | _ => 0

noncomputable def psiR (j : Fin 9) (y : ℝ) : Nat → ℝ
  | 0 => mu - phi (lo j)
  | 1 => mu - phi y
  | _ => mu - phi b

theorem valid_tailT (Bx : Box) (j : Fin 9) {fy : ℝ → ℝ → ℝ → ℝ} {y phiy : TM} (hy : Valid Bx fy y)
    (hp : Valid Bx (fun a b c => phi (fy a b c)) phiy) (k : Nat) :
    Valid Bx (fun a b c => tailR j (fy a b c) k) (tailT Bx j y phiy k) := by
  rcases k with _ | _ | k
  · exact valid_congr (valid_cqQ Bx C0Q) (fun _ _ _ _ => by simp [tailR, qR_C0Q])
  · exact valid_congr (valid_sub (valid_add (valid_ktT j Bx) hy) (valid_qm Bx (etaQ j) hp))
      (fun _ _ _ _ => by simp only [tailR, qR_etaQ])
  · exact valid_congr (valid_zeroT Bx) (fun _ _ _ _ => by simp [tailR])

theorem valid_psiT (Bx : Box) (j : Fin 9) {fy : ℝ → ℝ → ℝ → ℝ} {phiy : TM}
    (hp : Valid Bx (fun a b c => phi (fy a b c)) phiy) (k : Nat) :
    Valid Bx (fun a b c => psiR j (fy a b c) k) (psiT j phiy k) := by
  rcases k with _ | _ | k
  · exact valid_congr (valid_psiLoT j Bx) (fun _ _ _ _ => by simp [psiR])
  · exact valid_congr (valid_sub (valid_cqQ Bx muQ) hp) (fun _ _ _ _ => by simp [psiR, qR_muQ])
  · exact valid_congr (valid_psiBT Bx) (fun _ _ _ _ => by simp [psiR])

theorem tail_piece (j : Fin 9) (lo' hi' : Z) (y : ℝ) (hl : toR lo' ≤ y) (hh : y ≤ toR hi') :
    ∃ k ∈ pcs, tailOK j lo' hi' k = true ∧ tail j y = tailR j y k := by
  rw [le_toR_iff] at hl; rw [toR_le_iff] at hh
  obtain ⟨fb1, fb2⟩ := floorS_spec bQ d_bQ
  obtain ⟨ch1, ch2⟩ := ceilS_spec (hQ j) (d_hQ j)
  rw [qR_bQ] at fb1 fb2; rw [qR_hQ] at ch1 ch2
  have hS := SN_posR
  by_cases h1 : y ≤ b
  · refine ⟨0, by simp [pcs], ?_, by simp [tail, h1, tailR]⟩
    simp only [tailOK, zle_zv]
    have := mul_le_mul_of_nonneg_right h1 hS.le
    have : (zv lo' : ℝ) < zv (floorS bQ) + 1 := by linarith
    have : zv lo' < zv (floorS bQ) + 1 := by exact_mod_cast this
    omega
  by_cases h2 : y < h j
  · refine ⟨1, by simp [pcs], ?_, by simp [tail, h1, h2, tailR]; ring⟩
    simp only [tailOK, Bool.and_eq_true, zlt_zv]
    push Not at h1
    have := mul_lt_mul_of_pos_right h1 hS
    have := mul_lt_mul_of_pos_right h2 hS
    constructor
    · have : (zv (floorS bQ) : ℝ) < zv hi' := by linarith
      exact_mod_cast this
    · have : (zv lo' : ℝ) < zv (ceilS (hQ j)) := by linarith
      exact_mod_cast this
  · refine ⟨2, by simp [pcs], ?_, by simp [tail, h1, h2, tailR]⟩
    simp only [tailOK, zle_zv]
    push Not at h2
    have := mul_le_mul_of_nonneg_right h2 hS.le
    have : (zv (ceilS (hQ j)) : ℝ) < zv hi' + 1 := by linarith
    have : zv (ceilS (hQ j)) < zv hi' + 1 := by exact_mod_cast this
    omega

theorem rho_piece (j : Fin 9) (lo' hi' : Z) (y : ℝ) (hl : toR lo' ≤ y) (hh : y ≤ toR hi') :
    ∃ k ∈ pcs, rhoOK j lo' hi' k = true ∧ mu - phi (rho j y) = psiR j y k := by
  rw [le_toR_iff] at hl; rw [toR_le_iff] at hh
  obtain ⟨fb1, fb2⟩ := ceilS_spec bQ d_bQ
  obtain ⟨cl1, cl2⟩ := ceilS_spec (loQ j) (d_loQ j)
  obtain ⟨fh1, fh2⟩ := floorS_spec (hiQ j) (d_hiQ j)
  rw [qR_bQ] at fb1 fb2; rw [qR_loQ] at cl1 cl2; rw [qR_hiQ] at fh1 fh2
  have hS := SN_posR
  by_cases h1 : y < lo j
  · refine ⟨0, by simp [pcs], ?_, by simp [rho, h1, psiR]⟩
    simp only [rhoOK, zlt_zv]
    have := mul_lt_mul_of_pos_right h1 hS
    have : (zv lo' : ℝ) < zv (ceilS (loQ j)) := by linarith
    exact_mod_cast this
  by_cases h2 : y ≤ hi j
  · refine ⟨1, by simp [pcs], ?_, by simp [rho, h1, h2, psiR]⟩
    simp only [rhoOK, Bool.or_eq_true, Bool.and_eq_true, zle_zv]
    left
    push Not at h1
    have := mul_le_mul_of_nonneg_right h1 hS.le
    have := mul_le_mul_of_nonneg_right h2 hS.le
    constructor
    · have : (zv (ceilS (loQ j)) : ℝ) < zv hi' + 1 := by linarith
      have : zv (ceilS (loQ j)) < zv hi' + 1 := by exact_mod_cast this
      omega
    · have : (zv lo' : ℝ) < zv (floorS (hiQ j)) + 1 := by linarith
      have : zv lo' < zv (floorS (hiQ j)) + 1 := by exact_mod_cast this
      omega
  by_cases h3 : y < b
  · refine ⟨2, by simp [pcs], ?_, by simp [rho, h1, h2, h3, psiR]⟩
    simp only [rhoOK, Bool.and_eq_true, zlt_zv]
    push Not at h2
    have := mul_lt_mul_of_pos_right h2 hS
    have := mul_lt_mul_of_pos_right h3 hS
    constructor
    · have : (zv (floorS (hiQ j)) : ℝ) < zv hi' := by linarith
      exact_mod_cast this
    · have : (zv lo' : ℝ) < zv (ceilS bQ) := by linarith
      exact_mod_cast this
  · refine ⟨1, by simp [pcs], ?_, by simp [rho, h1, h2, h3, psiR]⟩
    simp only [rhoOK, Bool.or_eq_true, Bool.and_eq_true, zle_zv]
    right
    push Not at h3
    have := mul_le_mul_of_nonneg_right h3 hS.le
    have : (zv (ceilS bQ) : ℝ) < zv hi' + 1 := by linarith
    have : zv (ceilS bQ) < zv hi' + 1 := by exact_mod_cast this
    omega

theorem zero_le_lower {Bx : Box} {f : ℝ → ℝ → ℝ → ℝ} {t : TM} (hv : Valid Bx f t)
    (hc : zle zero (lower Bx t) = true) {x0 x1 x2 : ℝ} (hx : InBox Bx x0 x1 x2) : 0 ≤ f x0 x1 x2 := by
  rw [zle_iff, toR_zero] at hc
  exact hc.trans (lower_le hv hx)


/-! ### Families -/

theorem fam1_sound {Bx : Box} {a F MB phia tau : TM} {fa fF fMB ftau : ℝ → ℝ → ℝ → ℝ}
    (j : Fin 9) (ha : Valid Bx fa a) (hF : Valid Bx fF F)
    (hMB : Valid Bx fMB MB) (hpa : Valid Bx (fun x y z => phi (fa x y z)) phia)
    (htau : Valid Bx ftau tau)
    (hc : fam1 Bx a F MB phia tau (lower Bx a) (upper Bx a) j = true)
    {x0 x1 x2 : ℝ} (hx : InBox Bx x0 x1 x2) :
    0 ≤ fF x0 x1 x2 * (tail j (fa x0 x1 x2) - fa x0 x1 x2 -
      ftau x0 x1 x2 * (mu - phi (rho j (fa x0 x1 x2)))) - fMB x0 x1 x2 := by
  obtain ⟨ka, hka, oka, eka⟩ := tail_piece j _ _ _ (lower_le ha hx) (le_upper ha hx)
  obtain ⟨kr, hkr, okr, ekr⟩ := rho_piece j _ _ _ (lower_le ha hx) (le_upper ha hx)
  unfold fam1 at hc
  rw [List.all_eq_true] at hc
  have h1 := hc ka hka
  simp only [oka, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  have h3 := h1 kr hkr
  simp only [okr, Bool.not_true, Bool.false_or] at h3
  have hv := valid_sub (valid_mul hF (valid_sub (valid_sub (valid_tailT Bx j ha hpa ka) ha)
    (valid_mul htau (valid_psiT Bx j hpa kr)))) hMB
  have := zero_le_lower hv h3 hx
  rw [eka, ekr]
  exact this

/-! ### Multipliers -/

noncomputable def Fv (cd : CellData) (p : ℝ) : ℝ :=
  if cd.l2.n.p = cd.l2.n.n then 1 - p else (mu * p - Phi p) * (1 - p)

noncomputable def Mv (cd : CellData) (p : ℝ) : ℝ :=
  if cd.l2.n.p = cd.l2.n.n then qR cd.l0 + qR cd.l1 * p
  else (qR cd.l0 + qR cd.l1 * p) * (mu * p - Phi p) + qR cd.l2 * (p * (1 - p))

theorem valid_DT {Bx : Box} {P : TM} (hP : Valid Bx (fun _ p _ => p) P) :
    Valid Bx (fun _ p _ => mu * p - Phi p) (DT Bx P) :=
  valid_congr (valid_sub (valid_qm Bx muQ hP) (valid_PhiT (valid_pows hP)))
    (fun _ _ _ _ => by simp only [qR_muQ])

theorem valid_L (cd : CellData) {Bx : Box} {P : TM} (hP : Valid Bx (fun _ p _ => p) P) :
    Valid Bx (fun _ p _ => qR cd.l0 + qR cd.l1 * p) (add (cqQ cd.l0) (qm Bx cd.l1 P)) :=
  valid_add (valid_cqQ Bx cd.l0) (valid_qm Bx cd.l1 hP)

theorem beq_true {a b : Nat} (hl : a = b) : Nat.beq a b = true := by simpa using hl
theorem beq_false {a b : Nat} (hl : ¬ a = b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) hl

theorem valid_mulF (cd : CellData) {Bx : Box} {P : TM} (hP : Valid Bx (fun _ p _ => p) P) :
    Valid Bx (fun _ p _ => Fv cd p) (mulF cd Bx P) := by
  unfold mulF
  by_cases hl : cd.l2.n.p = cd.l2.n.n
  · rw [beq_true hl, cond_true]
    exact valid_congr (valid_sub (valid_one Bx) hP) (fun _ _ _ _ => by simp [Fv, hl])
  · rw [beq_false hl, cond_false]
    exact valid_congr (valid_mul (valid_DT hP) (valid_sub (valid_one Bx) hP))
      (fun _ _ _ _ => by simp [Fv, hl])

theorem valid_mulM (cd : CellData) {Bx : Box} {P : TM} (hP : Valid Bx (fun _ p _ => p) P) :
    Valid Bx (fun _ p _ => Mv cd p) (mulM cd Bx P) := by
  unfold mulM
  by_cases hl : cd.l2.n.p = cd.l2.n.n
  · rw [beq_true hl, cond_true]
    exact valid_congr (valid_L cd hP) (fun _ _ _ _ => by simp [Mv, hl])
  · rw [beq_false hl, cond_false]
    exact valid_congr (valid_add (valid_mul (valid_L cd hP) (valid_DT hP))
      (valid_qm Bx cd.l2 (valid_mul hP (valid_sub (valid_one Bx) hP))))
      (fun _ _ _ _ => by simp [Mv, hl])

theorem valid_tauT (cd : CellData) (j : Fin 9) {Bx : Box} {P : TM}
    (hP : Valid Bx (fun _ p _ => p) P) : Valid Bx (fun _ p _ => tauv cd j p) (tauT cd Bx j P) :=
  valid_mul hP (valid_add (valid_cqQ Bx (cd.t0 j)) (valid_qm Bx (cd.t1 j) hP))

theorem qR_zero_of {q : Q} (hl : q.n.p = q.n.n) : qR q = 0 := by
  simp [qR, hl]

theorem lam_alg (cd : CellData) (p E Bv : ℝ) (hp1 : p < 1)
    (hD : ¬ cd.l2.n.p = cd.l2.n.n → 0 < mu * p - Phi p) (h0 : 0 ≤ Fv cd p * E - Mv cd p * Bv) :
    0 ≤ E - lamv cd p * Bv := by
  have h1 : (0 : ℝ) < 1 - p := by linarith
  by_cases hl : cd.l2.n.p = cd.l2.n.n
  · simp only [Fv, Mv, hl, if_true] at h0
    have e : E - lamv cd p * Bv = ((1 - p) * E - (qR cd.l0 + qR cd.l1 * p) * Bv) / (1 - p) := by
      unfold lamv; rw [qR_zero_of hl]; field_simp; ring
    rw [e]; exact div_nonneg h0 h1.le
  · have hD' := hD hl
    simp only [Fv, Mv, hl, if_false] at h0
    have e : E - lamv cd p * Bv = ((mu * p - Phi p) * (1 - p) * E - ((qR cd.l0 + qR cd.l1 * p) *
        (mu * p - Phi p) + qR cd.l2 * (p * (1 - p))) * Bv) / ((mu * p - Phi p) * (1 - p)) := by
      unfold lamv
      generalize mu * p - Phi p = D at hD' ⊢
      have := hD'.ne'; have := h1.ne'
      field_simp
    rw [e]; exact div_nonneg h0 (by positivity)

theorem Phi_one : Phi 1 = mu := by norm_num [Phi, mu]

/-! ### Leaves -/

theorem leaf1_sound (cd : CellData) (Bx : Box) (hc : leaf1 cd Bx = true) (w p v : ℝ)
    (hx : InBox Bx w p v) (hp1 : p < 1) (hD : ¬ cd.l2.n.p = cd.l2.n.n → 0 < mu * p - Phi p)
    (j : Fin 9) : 0 ≤ G1 j (lamv cd p) (tauv cd j p) (p - p * w) p := by
  have hP : Valid Bx (fun _ p _ => p) (var1 Bx) := valid_var1 Bx
  have hs : Valid Bx (fun w p _ => p * w) (mul Bx (var1 Bx) (var0 Bx)) := valid_mul hP (valid_var0 Bx)
  have ha : Valid Bx (fun w p _ => p - p * w) (sub (var1 Bx) (mul Bx (var1 Bx) (var0 Bx))) :=
    valid_sub hP hs
  have hy := valid_sub (valid_one Bx) hs
  have hBt : Valid Bx (fun w p _ => B (p - p * w) p 1)
      (sub (add (PhiT Bx (pows Bx (sub (var1 Bx) (mul Bx (var1 Bx) (var0 Bx))))) (cqQ muQ))
        (add (PhiT Bx (pows Bx (sub (cnst S) (mul Bx (var1 Bx) (var0 Bx))))) (qm Bx muQ (var1 Bx)))) :=
    valid_congr (valid_sub (valid_add (valid_PhiT (valid_pows ha)) (valid_cqQ Bx muQ))
      (valid_add (valid_PhiT (valid_pows hy)) (valid_qm Bx muQ hP))) (fun w p v _ => by
        simp only [B, qR_muQ, Phi_one]
        rw [show p - p * w + 1 - p = 1 - p * w by ring]; ring)
  have hMB := valid_mul (valid_mulM cd hP) hBt
  unfold leaf1 leaf1a leaf1b leaf1c at hc
  rw [List.all_eq_true] at hc
  have hf := fam1_sound j ha (valid_mulF cd hP) hMB (valid_phiT (valid_pows ha))
    (valid_tauT cd j hP) (hc j (List.mem_finRange j)) hx
  have := lam_alg cd p _ _ hp1 hD hf
  unfold G1; linarith

/-! ### Root checks -/

theorem zv_zadd (a b : Z) : zv (zadd a b) = zv a + zv b := by
  unfold zv; rw [zadd_p, zadd_n]; push_cast; ring

theorem zv_zmul (a b : Z) : zv (zmul a b) = zv a * zv b := by
  unfold zv; rw [zmul_p, zmul_n]; push_cast; ring

theorem zv_nat (d : Nat) : zv ⟨d, 0⟩ = d := by simp [zv]

theorem zv_zero : zv zero = 0 := by simp [zv, zero]

theorem linNonneg_sound {q0 q1 : Q} {x : Z} (hc : linNonneg q0 q1 x = true) :
    0 < q0.d ∧ 0 < q1.d ∧ 0 ≤ qR q0 + qR q1 * toR x := by
  unfold linNonneg at hc
  simp only [Bool.and_eq_true, Nat.blt_eq, zle_zv] at hc
  obtain ⟨⟨hd0, hd1⟩, hz⟩ := hc
  refine ⟨hd0, hd1, ?_⟩
  rw [zv_zero, zv_zadd, zv_zmul, zv_zmul, zv_zmul, zv_zmul, zv_nat, zv_nat] at hz
  have hS : zv S = SN := by simp [zv, S, SN]
  rw [hS] at hz
  have hzR : (0 : ℝ) ≤ zv q0.n * q1.d * SN + zv q1.n * q0.d * zv x := by exact_mod_cast hz
  have hd0R : (0 : ℝ) < q0.d := by exact_mod_cast hd0
  have hd1R : (0 : ℝ) < q1.d := by exact_mod_cast hd1
  have hSR := SN_posR
  have e : qR q0 + qR q1 * toR x =
      (zv q0.n * q1.d * SN + zv q1.n * q0.d * zv x) / (q0.d * q1.d * SN) := by
    rw [qR_eq, qR_eq, toR_eq]; field_simp
  rw [e]; positivity

theorem lin_interp {c0 c1 x y p : ℝ} (hx : 0 ≤ c0 + c1 * x) (hy : 0 ≤ c0 + c1 * y)
    (h1 : x ≤ p) (h2 : p ≤ y) : 0 ≤ c0 + c1 * p := by
  rcases le_total 0 c1 with hc | hc
  · nlinarith [mul_le_mul_of_nonneg_left h1 hc]
  · nlinarith [mul_le_mul_of_nonpos_left h2 hc]

theorem lin_ok {q0 q1 : Q} {x y : Z} {p : ℝ} (hx : linNonneg q0 q1 x = true)
    (hy : linNonneg q0 q1 y = true) (h1 : toR x ≤ p) (h2 : p ≤ toR y) :
    0 ≤ qR q0 + qR q1 * p :=
  lin_interp (linNonneg_sound hx).2.2 (linNonneg_sound hy).2.2 h1 h2

theorem abs_cell {cd : CellData} {p : ℝ} (hlo : toR (zsub cd.pm cd.ph) ≤ p)
    (hhi : p ≤ toR (zadd cd.pm cd.ph)) : |p - toR cd.pm| ≤ toR cd.ph := by
  rw [toR_zsub] at hlo; rw [toR_zadd] at hhi
  rw [abs_le]; constructor <;> linarith

theorem toR_half : toR half = 1 / 2 := by norm_num [toR, half, SN]

theorem abs_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : |x - toR half| ≤ toR half := by
  rw [toR_half, abs_le]; constructor <;> linarith

theorem abs_zero' (x : ℝ) (hx : x = 0) : |x - toR zero| ≤ toR zero := by
  simp [hx, toR_zero]

theorem tau_ok (cd : CellData) (j : Fin 9) {x y : Z} {p : ℝ} (hp0 : 0 ≤ p)
    (hx : linNonneg (cd.t0 j) (cd.t1 j) x = true) (hy : linNonneg (cd.t0 j) (cd.t1 j) y = true)
    (h1 : toR x ≤ p) (h2 : p ≤ toR y) : 0 ≤ tauv cd j p :=
  mul_nonneg hp0 (lin_ok hx hy h1 h2)

/-! ### Main theorem -/

theorem G1_of_leaf1 (cd : CellData) (hr : ¬ cd.l2.n.p = cd.l2.n.n → ∀ p : ℝ,
      toR (zsub cd.pm cd.ph) ≤ p → p ≤ toR (zadd cd.pm cd.ph) → 0 < mu * p - Phi p)
    (hp1 : toR (zadd cd.pm cd.ph) < 1)
    (ht : runAll (leaf1 cd) (root1 cd) cd.tree1 = true) (p : ℝ) (hp : 0 < p)
    (hlo : toR (zsub cd.pm cd.ph) ≤ p)
    (hhi : p ≤ toR (zadd cd.pm cd.ph)) (j : Fin 9) (a : ℝ) (ha0 : 0 ≤ a) (hap : a ≤ p) :
    0 ≤ G1 j (lamv cd p) (tauv cd j p) a p := by
  have hw0 : 0 ≤ 1 - a / p := by rw [sub_nonneg, div_le_one hp]; exact hap
  have hw1 : 1 - a / p ≤ 1 := by have := div_nonneg ha0 hp.le; linarith
  have hb : InBox (root1 cd) (1 - a / p) p 0 :=
    ⟨abs_half hw0 hw1, abs_cell hlo hhi, abs_zero' 0 rfl⟩
  have := runAll_sound (leaf1 cd) (fun w p _ => toR (zsub cd.pm cd.ph) ≤ p →
      p ≤ toR (zadd cd.pm cd.ph) → ∀ j, 0 ≤ G1 j (lamv cd p) (tauv cd j p) (p - p * w) p)
    (fun Bx hB x0 x1 x2 hx h1 h2 j => leaf1_sound cd Bx hB x0 x1 x2 hx (by linarith)
      (fun hl => hr hl x1 h1 h2) j) (root1 cd) cd.tree1 ht _ _ _ hb hlo hhi j
  have e : p - p * (1 - a / p) = a := by field_simp; ring
  rwa [e] at this

end RandomSizeStable.Stability.RankCutCert.Dev
end

section
/-! Soundness of the end-cell and p = 1 checkers (Blueprint). -/

set_option autoImplicit false

namespace RandomSizeStable.Stability.RankCutCert.Dev

/-! ### Divided differences -/

/-- The polynomial `Q(x, y) = (Phi y - Phi x)/(y - x)`. -/
noncomputable def Qp (x y : ℝ) : ℝ :=
  19 / 146 * (x + y) + 35 / 438 * (x ^ 2 + x * y + y ^ 2) +
    (y * ((x + y) * (x ^ 2 + y ^ 2) * (x ^ 4 + y ^ 4) * (x ^ 8 + y ^ 8) * (x ^ 16 + y ^ 16)) + x ^ 32) / 66

theorem Qp_mul (x y : ℝ) : (y - x) * Qp x y = Phi y - Phi x := by
  unfold Qp Phi; ring

/-- `K(a) = Phi(a)/a^2`. -/
noncomputable def Kp (a : ℝ) : ℝ := 19 / 146 + 35 / 438 * a + a ^ 31 / 66

theorem Phi_K (a : ℝ) : Phi a = a ^ 2 * Kp a := by unfold Phi Kp; ring

theorem valid_sqT {Bx : Box} {f : ℝ → ℝ → ℝ → ℝ} {t : TM} (k : ℕ)
    (ht : Valid Bx (fun a b c => f a b c ^ k) t) :
    Valid Bx (fun a b c => f a b c ^ (2 * k)) (sqT Bx t) :=
  valid_congr (valid_mul ht ht) (fun _ _ _ _ => by ring)

theorem valid_pow1 {Bx : Box} {f : ℝ → ℝ → ℝ → ℝ} {t : TM} (ht : Valid Bx f t) :
    Valid Bx (fun a b c => f a b c ^ 1) t :=
  valid_congr ht (fun _ _ _ _ => by ring)

theorem valid_QT {Bx : Box} {fx fy : ℝ → ℝ → ℝ → ℝ} {x y : TM} (hx : Valid Bx fx x)
    (hy : Valid Bx fy y) : Valid Bx (fun a b c => Qp (fx a b c) (fy a b c)) (QT Bx x y) := by
  have x2 := valid_sqT 1 (valid_pow1 hx)
  have y2 := valid_sqT 1 (valid_pow1 hy)
  have x4 := valid_sqT _ x2
  have y4 := valid_sqT _ y2
  have x8 := valid_sqT _ x4
  have y8 := valid_sqT _ y4
  have x16 := valid_sqT _ x8
  have y16 := valid_sqT _ y8
  have x32 := valid_sqT _ x16
  unfold QT QT1 H32c
  exact valid_congr (valid_add (valid_add (valid_qmul ⟨19, 0⟩ 146 (by norm_num) (valid_add hx hy))
    (valid_qmul ⟨35, 0⟩ 438 (by norm_num) (valid_add (valid_add x2 (valid_mul hx hy)) y2)))
    (valid_qmul ⟨1, 0⟩ 66 (by norm_num) (valid_add (valid_mul hy (valid_mul (valid_mul (valid_mul
      (valid_mul (valid_add hx hy) (valid_add x2 y2)) (valid_add x4 y4)) (valid_add x8 y8))
      (valid_add x16 y16))) x32)))
    (fun a b c _ => by simp only [Qp, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, sub_zero]; ring)

theorem valid_KT {Bx : Box} {fx : ℝ → ℝ → ℝ → ℝ} {x : TM} (hx : Valid Bx fx x) :
    Valid Bx (fun a b c => Kp (fx a b c)) (KT Bx x) := by
  have x2 := valid_sqT 1 (valid_pow1 hx)
  have x4 := valid_sqT _ x2
  have x8 := valid_sqT _ x4
  have x16 := valid_sqT _ x8
  unfold KT KT1
  exact valid_congr (valid_add (valid_add (valid_cq Bx ⟨19, 0⟩ 146 (by norm_num))
    (valid_qmul ⟨35, 0⟩ 438 (by norm_num) hx))
    (valid_qmul ⟨1, 0⟩ 66 (by norm_num) (valid_mul x16 (valid_mul x8 (valid_mul x4 (valid_mul x2 hx))))))
    (fun a b c _ => by simp only [Kp, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, sub_zero]; ring)

theorem B_caseZ (p w v : ℝ) : B (p - p * w) p (p + (1 - p) * v) =
    p * ((1 - w) * (1 - w) * p * Kp (p - p * w) +
      w * Qp (p + (1 - p) * v - p * w) (p + (1 - p) * v) - mu) := by
  have e := Qp_mul (p + (1 - p) * v - p * w) (p + (1 - p) * v)
  have e2 := Phi_K (p - p * w)
  unfold B
  rw [show p - p * w + (p + (1 - p) * v) - p = p + (1 - p) * v - p * w by ring]
  linear_combination e2 - e

/-! ### The tail is nonincreasing -/

noncomputable def phidD (x : ℝ) : ℝ := 19 / 73 + 35 / 73 * x + 16 * x ^ 31

theorem bD_pos : 0 < b := by norm_num [b]

theorem etaD_pos (j : Fin 9) : 0 < eta j := by fin_cases j <;> norm_num [eta]

theorem one_le_eta_phidD (j : Fin 9) : 1 ≤ eta j * phidD b := by
  fin_cases j <;> norm_num [eta, phidD, b]

theorem C0_ge (j : Fin 9) : eta j * (phi (h j) - phi b) - (h j - b) ≤ C0 := by
  fin_cases j <;> norm_num [eta, phi, h, b, C0]

theorem bD_le_h (j : Fin 9) : b ≤ h j := by fin_cases j <;> norm_num [b, h]

theorem phi_sub_ge {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    phidD x * (y - x) ≤ phi y - phi x := by
  have hy : 0 ≤ y := hx.trans hxy
  have e : phi y - phi x = (y - x) * (19 / 73 + 35 / 146 * (x + y) +
      ((x + y) * (x ^ 2 + y ^ 2) * (x ^ 4 + y ^ 4) * (x ^ 8 + y ^ 8) * (x ^ 16 + y ^ 16)) / 2) := by
    unfold phi; ring
  have f1 : 2 * x ≤ x + y := by linarith
  have f2 : 2 * x ^ 2 ≤ x ^ 2 + y ^ 2 := by have := pow_le_pow_left₀ hx hxy 2; linarith
  have f4 : 2 * x ^ 4 ≤ x ^ 4 + y ^ 4 := by have := pow_le_pow_left₀ hx hxy 4; linarith
  have f8 : 2 * x ^ 8 ≤ x ^ 8 + y ^ 8 := by have := pow_le_pow_left₀ hx hxy 8; linarith
  have f16 : 2 * x ^ 16 ≤ x ^ 16 + y ^ 16 := by have := pow_le_pow_left₀ hx hxy 16; linarith
  have hP : 2 * x * (2 * x ^ 2) * (2 * x ^ 4) * (2 * x ^ 8) * (2 * x ^ 16) ≤
      (x + y) * (x ^ 2 + y ^ 2) * (x ^ 4 + y ^ 4) * (x ^ 8 + y ^ 8) * (x ^ 16 + y ^ 16) := by
    gcongr
  have e2 : 2 * x * (2 * x ^ 2) * (2 * x ^ 4) * (2 * x ^ 8) * (2 * x ^ 16) = 32 * x ^ 31 := by ring
  rw [e, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  unfold phidD
  nlinarith

theorem gmono (j : Fin 9) {x y : ℝ} (hb : b ≤ x) (hxy : x ≤ y) :
    y - x ≤ eta j * (phi y - phi x) := by
  have hx : 0 ≤ x := bD_pos.le.trans hb
  have h1 := phi_sub_ge hx hxy
  have h2 : phidD b ≤ phidD x := by
    unfold phidD
    have := pow_le_pow_left₀ bD_pos.le hb 31
    nlinarith
  have h3 := one_le_eta_phidD j
  have h4 := etaD_pos j
  have h5 : 0 ≤ y - x := by linarith
  have : eta j * (phidD x * (y - x)) ≤ eta j * (phi y - phi x) := mul_le_mul_of_nonneg_left h1 h4.le
  have : (y - x) ≤ eta j * phidD x * (y - x) := by
    have : 1 ≤ eta j * phidD x := h3.trans (mul_le_mul_of_nonneg_left h2 h4.le)
    nlinarith
  nlinarith

theorem tail_anti (j : Fin 9) {x y : ℝ} (hxy : x ≤ y) : tail j y ≤ tail j x := by
  have hC := C0_ge j
  have hbh := bD_le_h j
  unfold tail
  by_cases hy : y ≤ b
  · have hx : x ≤ b := hxy.trans hy
    simp [hx, hy]
  by_cases hx : x ≤ b
  · simp only [hx, hy, if_true, if_false]
    by_cases hyh : y < h j
    · simp only [hyh, if_true]
      have := gmono j le_rfl (le_of_lt (not_le.mp hy))
      linarith
    · simp only [hyh, if_false]
      have : (0 : ℝ) ≤ C0 := by norm_num [C0]
      exact this
  · simp only [hx, hy, if_false]
    push Not at hx
    by_cases hxh : x < h j
    · by_cases hyh : y < h j
      · simp only [hxh, hyh, if_true]
        have := gmono j hx.le hxy
        linarith
      · simp only [hxh, hyh, if_true, if_false]
        have := gmono j hx.le hxh.le
        linarith
    · have hyh : ¬ y < h j := fun hh => hxh (lt_of_le_of_lt hxy hh)
      simp [hxh, hyh]

/-! ### Families of the end checkers -/

theorem famZ2_sound {Bx : Box} {a A om p1 LB phia phiA tau u : TM}
    {fa fA fom fp1 fLB ftau fu : ℝ → ℝ → ℝ → ℝ}
    (j : Fin 9) (ha : Valid Bx fa a) (hA : Valid Bx fA A) (hom : Valid Bx fom om)
    (hp1 : Valid Bx fp1 p1) (hLB : Valid Bx fLB LB)
    (hpa : Valid Bx (fun x y z => phi (fa x y z)) phia)
    (hpA : Valid Bx (fun x y z => phi (fA x y z)) phiA) (htau : Valid Bx ftau tau)
    (hu : Valid Bx fu u)
    (hc : famZ2 Bx a A om p1 LB phia phiA tau (lower Bx a) (upper Bx a) (lower Bx A) (upper Bx A)
      u j = true)
    {x0 x1 x2 : ℝ} (hx : InBox Bx x0 x1 x2) :
    0 ≤ fom x0 x1 x2 * (tail j (fa x0 x1 x2) - tail j (fA x0 x1 x2) - fp1 x0 x1 x2 * fu x0 x1 x2 -
      fp1 x0 x1 x2 * (ftau x0 x1 x2 * (mu - phi (rho j (fA x0 x1 x2))))) - fLB x0 x1 x2 := by
  obtain ⟨ka, hka, oka, eka⟩ := tail_piece j _ _ _ (lower_le ha hx) (le_upper ha hx)
  obtain ⟨kA, hkA, okA, ekA⟩ := tail_piece j _ _ _ (lower_le hA hx) (le_upper hA hx)
  obtain ⟨kr, hkr, okr, ekr⟩ := rho_piece j _ _ _ (lower_le hA hx) (le_upper hA hx)
  unfold famZ2 at hc
  rw [List.all_eq_true] at hc
  have h1 := hc ka hka
  simp only [oka, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  have h2 := h1 kA hkA
  simp only [okA, Bool.not_true, Bool.false_or, List.all_eq_true] at h2
  have h3 := h2 kr hkr
  simp only [okr, Bool.not_true, Bool.false_or] at h3
  have hv := valid_sub (valid_mul hom (valid_sub (valid_sub (valid_sub
    (valid_tailT Bx j ha hpa ka) (valid_tailT Bx j hA hpA kA)) (valid_mul hp1 hu))
    (valid_mul hp1 (valid_mul htau (valid_psiT Bx j hpA kr))))) hLB
  have := zero_le_lower hv h3 hx
  rw [eka, ekA, ekr]
  exact this

/-! ### Leaves of the end checkers -/

theorem lamv_of_l2 (cd : CellData) (hl2 : qR cd.l2 = 0) (p : ℝ) :
    lamv cd p = (qR cd.l0 + qR cd.l1 * p) / (1 - p) := by
  unfold lamv; rw [hl2]; simp

theorem leafZ2_sound (cd : CellData) (Bx : Box) (hc : leafZ2 cd Bx = true) (w p v : ℝ)
    (hx : InBox Bx w p v) (hp0 : 0 < p) (hp1 : p < 1) (hpp : p ≤ toR (zadd cd.pm cd.ph))
    (hl2 : qR cd.l2 = 0) (haA : p - p * w ≤ p + (1 - p) * v)
    (j : Fin 9) : 0 ≤ G2 j (lamv cd p) (tauv cd j p) (p - p * w) p (p + (1 - p) * v) := by
  have hP : Valid Bx (fun _ p _ => p) (var1 Bx) := valid_var1 Bx
  have hW : Valid Bx (fun w _ _ => w) (var0 Bx) := valid_var0 Bx
  have hs : Valid Bx (fun w p _ => p * w) (mul Bx (var1 Bx) (var0 Bx)) := valid_mul hP hW
  have ha : Valid Bx (fun w p _ => p - p * w) (sub (var1 Bx) (mul Bx (var1 Bx) (var0 Bx))) :=
    valid_sub hP hs
  have hA : Valid Bx (fun _ p v => p + (1 - p) * v)
      (add (var1 Bx) (mul Bx (sub (cnst S) (var1 Bx)) (var2 Bx))) :=
    valid_add hP (valid_mul (valid_sub (valid_one Bx) hP) (valid_var2 Bx))
  have hu : Valid Bx (fun w _ _ => 1 - w) (sub (cnst S) (var0 Bx)) := valid_sub (valid_one Bx) hW
  have hp1T := valid_cnst Bx (zadd cd.pm cd.ph)
  have hX := valid_sub (valid_add (valid_mul (valid_mul (valid_mul hu hu) hP) (valid_KT ha))
    (valid_mul hW (valid_QT (valid_sub hA (valid_mul hP hW)) hA))) (valid_cqQ Bx muQ)
  have hLB := valid_mul (valid_mul hp1T (valid_L cd hP)) hX
  have htau' : Valid Bx (fun _ p _ => qR (cd.t0 j) + qR (cd.t1 j) * p)
      (add (cqQ (cd.t0 j)) (qm Bx (cd.t1 j) (var1 Bx))) :=
    valid_add (valid_cqQ Bx (cd.t0 j)) (valid_qm Bx (cd.t1 j) hP)
  unfold leafZ2 leafZ2a leafZ2b at hc
  rw [List.all_eq_true] at hc
  have hf := famZ2_sound j ha hA (valid_sub (valid_one Bx) hP) hp1T hLB
    (valid_phiT (valid_pows ha)) (valid_phiT (valid_pows hA)) htau' hu
    (hc j (List.mem_finRange j)) hx
  simp only [qR_muQ] at hf
  have hq : 0 < 1 - p := by linarith
  have hlB : (1 - p) * (lamv cd p * B (p - p * w) p (p + (1 - p) * v)) =
      (qR cd.l0 + qR cd.l1 * p) * (p * ((1 - w) * (1 - w) * p * Kp (p - p * w) +
      w * Qp (p + (1 - p) * v - p * w) (p + (1 - p) * v) - mu)) := by
    rw [lamv_of_l2 cd hl2, B_caseZ]; field_simp
  set p1 := toR (zadd cd.pm cd.ph)
  set L := qR cd.l0 + qR cd.l1 * p
  set X := (1 - w) * (1 - w) * p * Kp (p - p * w) +
      w * Qp (p + (1 - p) * v - p * w) (p + (1 - p) * v) - mu
  set R := tail j (p - p * w) - tail j (p + (1 - p) * v)
  set ps := mu - phi (rho j (p + (1 - p) * v))
  have hR : 0 ≤ R := sub_nonneg.mpr (tail_anti j haA)
  have hchk : 0 ≤ (1 - p) * (R - p1 * (1 - w) - p1 * ((qR (cd.t0 j) + qR (cd.t1 j) * p) * ps)) -
      p1 * L * X := hf
  have key : (1 - p) * p1 * G2 j (lamv cd p) (tauv cd j p) (p - p * w) p (p + (1 - p) * v) =
      p * ((1 - p) * (R - p1 * (1 - w) - p1 * ((qR (cd.t0 j) + qR (cd.t1 j) * p) * ps)) -
        p1 * L * X) + (1 - p) * R * (p1 - p) := by
    unfold G2 tauv
    linear_combination (-p1) * hlB
  have hpos : 0 < (1 - p) * p1 := mul_pos hq (by linarith)
  have rhs : 0 ≤ p * ((1 - p) * (R - p1 * (1 - w) - p1 * ((qR (cd.t0 j) + qR (cd.t1 j) * p) * ps)) -
        p1 * L * X) + (1 - p) * R * (p1 - p) :=
    add_nonneg (mul_nonneg hp0.le hchk) (mul_nonneg (mul_nonneg hq.le hR) (by linarith))
  rw [← key] at rhs
  exact (mul_nonneg_iff_of_pos_left hpos).mp rhs

/-! ### Main theorems -/

theorem root0_sound (cd : CellData) (hr : rootOK0 cd = true) :
    qR cd.l2 = 0 ∧ cd.l2.n.p = cd.l2.n.n ∧ ∀ p : ℝ, 0 ≤ p → p < 1 →
      toR (zsub cd.pm cd.ph) ≤ p → p ≤ toR (zadd cd.pm cd.ph) →
      0 ≤ lamv cd p ∧ ∀ j, 0 ≤ tauv cd j p := by
  unfold rootOK0 at hr
  simp only [Bool.and_eq_true, List.all_eq_true] at hr
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hr
  have e3 := Nat.eq_of_beq_eq_true h3
  have e4 := Nat.eq_of_beq_eq_true h4
  have hl : cd.l2.n.p = cd.l2.n.n := by rw [e3, e4]
  have hq := qR_zero_of hl
  refine ⟨hq, hl, fun p hp0 hp1 hlo hhi => ⟨?_, fun j => ?_⟩⟩
  · rw [lamv_of_l2 cd hq]; exact div_nonneg (lin_ok h1 h2 hlo hhi) (by linarith)
  · have := h5 j (List.mem_finRange j)
    exact tau_ok cd j hp0 this.1 this.2 hlo hhi

theorem cell0Check_sound (cd : CellData) (h : cell0Check cd = true) : Cell0Stmt cd := by
  unfold cell0Check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨_, _⟩, hlt⟩, hr⟩, ht1⟩, ht2⟩ := h
  rw [zlt_iff, toR_S] at hlt
  obtain ⟨hq, hl, hroot⟩ := root0_sound cd hr
  intro p hp hlo hhi
  have hp1 : p < 1 := by linarith
  obtain ⟨hlam, htau⟩ := hroot p hp.le hp1 hlo hhi
  refine ⟨hlam, htau, fun j a A ha0 hap hpA hA1 => ⟨?_, ?_⟩⟩
  · exact G1_of_leaf1 cd (fun hl' => absurd hl hl') hlt ht1 p hp hlo hhi j a ha0 hap
  · have hq1 : 0 < 1 - p := by linarith
    have hw0 : 0 ≤ 1 - a / p := by rw [sub_nonneg, div_le_one hp]; exact hap
    have hw1 : 1 - a / p ≤ 1 := by have := div_nonneg ha0 hp.le; linarith
    have hv0 : 0 ≤ (A - p) / (1 - p) := div_nonneg (by linarith) hq1.le
    have hv1 : (A - p) / (1 - p) ≤ 1 := by rw [div_le_one hq1]; linarith
    have hb : InBox (root2 cd) (1 - a / p) p ((A - p) / (1 - p)) :=
      ⟨abs_half hw0 hw1, abs_cell hlo hhi, abs_half hv0 hv1⟩
    have e : p - p * (1 - a / p) = a := by field_simp; ring
    have e2 : p + (1 - p) * ((A - p) / (1 - p)) = A := by field_simp; ring
    have := runAll_sound (leafZ2 cd) (fun w p v => 0 < p → p < 1 → p ≤ toR (zadd cd.pm cd.ph) →
        p - p * w ≤ p + (1 - p) * v →
        ∀ j, 0 ≤ G2 j (lamv cd p) (tauv cd j p) (p - p * w) p (p + (1 - p) * v))
      (fun Bx hB x0 x1 x2 hx h0 h1 h2 h3 j => leafZ2_sound cd Bx hB x0 x1 x2 hx h0 h1 h2 hq h3 j)
      (root2 cd) cd.tree2 ht2 _ _ _ hb hp hp1 hhi (by rw [e, e2]; linarith) j
    rwa [e, e2] at this

end RandomSizeStable.Stability.RankCutCert.Dev
end

section
/-! The checker soundness theorems in the form of the published statements (`CellOK`, `P1OK`). -/

set_option autoImplicit false

namespace RandomSizeStable.Stability.RankCutCert

open Dev

theorem cell0Check_ok_dev (cd : CellData) (h : cell0Check cd = true) :
    CellOK (toR (zsub cd.pm cd.ph)) (toR (zadd cd.pm cd.ph)) (qR cd.l0) (qR cd.l1) (qR cd.l2)
      (fun j => qR (cd.t0 j)) (fun j => qR (cd.t1 j)) := by
  intro p hp0 _ h0 h1
  exact cell0Check_sound cd h p hp0 h0 h1

end RandomSizeStable.Stability.RankCutCert
end

open RandomSizeStable.Stability.RankCutCert in
theorem solution : type_of% @RandomSizeStable.Stability.RankCutCert.cell0Check_ok_dev := @RandomSizeStable.Stability.RankCutCert.cell0Check_ok_dev
