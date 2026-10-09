-- Prove2me | solution 1 for QueueingFundamentals.Transient.mm1_transient_bessel
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T18:24:28.331976+00:00
-- url     : https://prove2.me/submissions/99c44a89-64e6-4b12-9679-01385dc0f58a

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_besselI
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations
import Definitions.Def_QueueingFundamentals_Transient_mm1Transient

set_option autoImplicit false

namespace MM1Aux12395959
open QueueingFundamentals.Transient

/-- the `k`-th term of `I_m` -/
noncomputable def bt (m k : ℕ) (y : ℝ) : ℝ :=
  (y / 2) ^ (m + 2 * k) / ((Nat.factorial k : ℝ) * (Nat.factorial (m + k) : ℝ))

/-- its derivative -/
noncomputable def dbt (m k : ℕ) (y : ℝ) : ℝ :=
  ((m + 2 * k : ℕ) : ℝ) * (y / 2) ^ (m + 2 * k - 1) * (1 / 2) /
    ((Nat.factorial k : ℝ) * (Nat.factorial (m + k) : ℝ))

lemma besselI_eq (m : ℕ) (y : ℝ) : besselI m y = ∑' k, bt m k y := rfl

lemma nat_le_two_pow (N : ℕ) : (N : ℝ) ≤ 2 ^ N := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) N
  norm_num at hb
  linarith

lemma bt_abs_le (m k : ℕ) (y : ℝ) :
    |bt m k y| ≤ (|y| / 2) ^ m / (m.factorial : ℝ) * (((y / 2) ^ 2) ^ k / (k.factorial : ℝ)) := by
  unfold bt
  have hm : (0 : ℝ) < m.factorial := by positivity
  have hk : (0 : ℝ) < k.factorial := by positivity
  have hmk : (0 : ℝ) < (m + k).factorial := by positivity
  have hf : (m.factorial : ℝ) ≤ ((m + k).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_right m k)
  rw [abs_div, abs_pow, abs_div, abs_two, abs_of_pos (mul_pos hk hmk), pow_add, pow_mul]
  have e : ((|y| / 2) ^ 2) = (y / 2) ^ 2 := by rw [div_pow, div_pow, sq_abs]
  rw [e, div_le_iff₀ (mul_pos hk hmk)]
  have h0 : 0 ≤ (|y| / 2) ^ m / (m.factorial : ℝ) * (((y / 2) ^ 2) ^ k / (k.factorial : ℝ)) := by
    positivity
  calc (|y| / 2) ^ m * ((y / 2) ^ 2) ^ k
      = ((|y| / 2) ^ m / (m.factorial : ℝ) * (((y / 2) ^ 2) ^ k / (k.factorial : ℝ)))
          * ((k.factorial : ℝ) * (m.factorial : ℝ)) := by field_simp
    _ ≤ ((|y| / 2) ^ m / (m.factorial : ℝ) * (((y / 2) ^ 2) ^ k / (k.factorial : ℝ)))
          * ((k.factorial : ℝ) * ((m + k).factorial : ℝ)) := by gcongr

lemma bt_summable (m : ℕ) (y : ℝ) : Summable (fun k => bt m k y) :=
  Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial ((y / 2) ^ 2)).mul_left ((|y| / 2) ^ m / (m.factorial : ℝ)))
    (fun k => by rw [Real.norm_eq_abs]; exact bt_abs_le m k y)

lemma exp_hasSum (x : ℝ) : HasSum (fun k : ℕ => x ^ k / (k.factorial : ℝ)) (Real.exp x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp x
  rw [← Real.exp_eq_exp_ℝ] at h
  exact h

/-- T1(a): the growth bound -/
theorem besselI_abs_le (m : ℕ) (y : ℝ) :
    |besselI m y| ≤ (|y| / 2) ^ m / (m.factorial : ℝ) * Real.exp ((y / 2) ^ 2) := by
  have hsn : Summable (fun k => ‖bt m k y‖) := (bt_summable m y).norm
  have hb := (exp_hasSum ((y / 2) ^ 2)).mul_left ((|y| / 2) ^ m / (m.factorial : ℝ))
  rw [besselI_eq, ← Real.norm_eq_abs]
  calc ‖∑' k, bt m k y‖ ≤ ∑' k, ‖bt m k y‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ _ := hasSum_le (fun k => by rw [Real.norm_eq_abs]; exact bt_abs_le m k y) hsn.hasSum hb

/-- T1(d): value at 0 -/
theorem besselI_zero (m : ℕ) : besselI m 0 = if m = 0 then 1 else 0 := by
  rw [besselI_eq, tsum_eq_single 0 (fun k hk => by
    unfold bt
    rw [zero_div, zero_pow (by omega), zero_div])]
  unfold bt
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · rw [if_neg (by omega), zero_div, zero_pow (by omega), zero_div]

lemma bt_hasDerivAt (m k : ℕ) (y : ℝ) : HasDerivAt (bt m k) (dbt m k y) y := by
  have h1 : HasDerivAt (fun x : ℝ => (x / 2) ^ (m + 2 * k))
      (((m + 2 * k : ℕ) : ℝ) * (y / 2) ^ (m + 2 * k - 1) * (1 / 2)) y :=
    ((hasDerivAt_id' y).div_const 2).pow (m + 2 * k)
  exact h1.div_const _

lemma dbt_bound (m k : ℕ) (r : ℝ) (hr : 1 ≤ r) (z : ℝ) (hz : |z / 2| ≤ r) :
    ‖dbt m k z‖ ≤ (2 * r) ^ m * (((2 * r) ^ 2) ^ k / (k.factorial : ℝ)) := by
  unfold dbt
  have hk : (0 : ℝ) < k.factorial := by positivity
  have hmk : (1 : ℝ) ≤ (m + k).factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  set N := m + 2 * k with hN
  have hp : |z / 2| ^ (N - 1) ≤ r ^ N :=
    (pow_le_pow_left₀ (abs_nonneg _) hz _).trans (pow_le_pow_right₀ hr (Nat.sub_le N 1))
  have hNle := nat_le_two_pow N
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, Nat.abs_cast,
    abs_of_pos (mul_pos hk (by linarith : (0 : ℝ) < (m + k).factorial)),
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hnum : (N : ℝ) * |z / 2| ^ (N - 1) * (1 / 2) ≤ (2 * r) ^ N := by
    rw [mul_pow]
    have : (N : ℝ) * |z / 2| ^ (N - 1) ≤ 2 ^ N * r ^ N :=
      mul_le_mul hNle hp (by positivity) (by positivity)
    nlinarith [show (0 : ℝ) ≤ (N : ℝ) * |z / 2| ^ (N - 1) by positivity]
  rw [div_le_iff₀ (mul_pos hk (by linarith : (0 : ℝ) < (m + k).factorial))]
  have e : (2 * r) ^ m * (((2 * r) ^ 2) ^ k / (k.factorial : ℝ)) * (k.factorial : ℝ) = (2 * r) ^ N := by
    rw [hN, pow_add, pow_mul]; field_simp
  calc (N : ℝ) * |z / 2| ^ (N - 1) * (1 / 2) ≤ (2 * r) ^ N := hnum
    _ = (2 * r) ^ m * (((2 * r) ^ 2) ^ k / (k.factorial : ℝ)) * (k.factorial : ℝ) := e.symm
    _ ≤ (2 * r) ^ m * (((2 * r) ^ 2) ^ k / (k.factorial : ℝ)) *
          ((k.factorial : ℝ) * ((m + k).factorial : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith

lemma besselI_hasDerivAt_tsum (m : ℕ) (y : ℝ) :
    HasDerivAt (besselI m) (∑' k, dbt m k y) y := by
  set r : ℝ := |y| / 2 + 1 with hr
  have hr1 : 1 ≤ r := by have := abs_nonneg y; rw [hr]; linarith
  have hmem : ∀ z : ℝ, z ∈ Metric.ball (0 : ℝ) (|y| + 1) → |z / 2| ≤ r := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hz
    rw [abs_div, abs_two, hr]; linarith
  have key : HasDerivAt (fun z : ℝ => ∑' k, bt m k z) (∑' k, dbt m k y) y :=
    hasDerivAt_tsum_of_isPreconnected
      (u := fun k : ℕ => (2 * r) ^ m * (((2 * r) ^ 2) ^ k / (k.factorial : ℝ)))
      (g := fun (k : ℕ) (z : ℝ) => bt m k z)
      (g' := fun (k : ℕ) (z : ℝ) => dbt m k z)
      ((Real.summable_pow_div_factorial _).mul_left _) Metric.isOpen_ball
      (convex_ball (0 : ℝ) (|y| + 1)).isPreconnected
      (fun k z _ => bt_hasDerivAt m k z)
      (fun k z hz => dbt_bound m k r hr1 z (hmem z hz))
      (Metric.mem_ball_self (by positivity : (0 : ℝ) < |y| + 1))
      (bt_summable m 0)
      (by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith)
  exact key

/-- auxiliary: the `k`-weighted part -/
noncomputable def et (j k : ℕ) (y : ℝ) : ℝ :=
  (k : ℝ) * (y / 2) ^ (j + 2 * k) / ((Nat.factorial k : ℝ) * (Nat.factorial (j + 1 + k) : ℝ))

lemma dbt_succ_split (j k : ℕ) (y : ℝ) :
    dbt (j + 1) k y = (bt j k y + et j k y) / 2 := by
  unfold dbt bt et
  have e1 : j + 1 + 2 * k - 1 = j + 2 * k := by omega
  have e2 : j + 1 + k = (j + k) + 1 := by omega
  rw [e1, e2, Nat.factorial_succ]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  have : ((j + k).factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma et_succ (j k : ℕ) (y : ℝ) : et j (k + 1) y = bt (j + 2) k y := by
  unfold et bt
  have e1 : j + 2 * (k + 1) = j + 2 + 2 * k := by omega
  have e2 : j + 1 + (k + 1) = j + 2 + k := by omega
  rw [e1, e2, Nat.factorial_succ k]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  have : ((j + 2 + k).factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma dbt_zero_succ (k : ℕ) (y : ℝ) : dbt 0 (k + 1) y = bt 1 k y := by
  unfold dbt bt
  have e1 : 0 + 2 * (k + 1) - 1 = 1 + 2 * k := by omega
  have e2 : 0 + (k + 1) = k + 1 := by omega
  have e3 : 1 + k = k + 1 := by omega
  rw [e1, e2, e3, Nat.factorial_succ k]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- T1(b): `I_0' = I_1` -/
theorem besselI_hasDerivAt_zero (y : ℝ) : HasDerivAt (besselI 0) (besselI 1 y) y := by
  have h := besselI_hasDerivAt_tsum 0 y
  have hs : Summable (fun k => dbt 0 (k + 1) y) := by
    simp_rw [dbt_zero_succ]; exact bt_summable 1 y
  rw [tsum_eq_zero_add' (f := fun k => dbt 0 k y) hs] at h
  have h0 : dbt 0 0 y = 0 := by simp [dbt]
  simp_rw [dbt_zero_succ] at h
  rw [h0, zero_add] at h
  exact h

/-- T1(c): `I_{j+1}' = (I_j + I_{j+2}) / 2` -/
theorem besselI_hasDerivAt_succ (j : ℕ) (y : ℝ) :
    HasDerivAt (besselI (j + 1)) ((besselI j y + besselI (j + 2) y) / 2) y := by
  have h := besselI_hasDerivAt_tsum (j + 1) y
  have hes : Summable (fun k => et j (k + 1) y) := by
    simp_rw [et_succ]; exact bt_summable (j + 2) y
  have he : Summable (fun k => et j k y) := (summable_nat_add_iff 1).1 hes
  have hsplit : ∑' k, dbt (j + 1) k y = (∑' k, bt j k y + ∑' k, et j k y) / 2 := by
    simp_rw [dbt_succ_split]
    rw [tsum_div_const, (bt_summable j y).tsum_add he]
  have het : ∑' k, et j k y = besselI (j + 2) y := by
    rw [tsum_eq_zero_add' (f := fun k => et j k y) hes]
    simp_rw [et_succ]
    simp [et, besselI_eq]
  rw [hsplit, het, ← besselI_eq] at h
  exact h


/-! ## T3: the forward equations for the Bessel formula -/

noncomputable def alp (lam mu : ℝ) : ℝ := Real.sqrt (lam / mu)

lemma alp_pos (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) : 0 < alp lam mu :=
  Real.sqrt_pos.2 (div_pos hlam hmu)

lemma alp_sq (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) : alp lam mu ^ 2 = lam / mu :=
  Real.sq_sqrt (div_pos hlam hmu).le

lemma sqrt_eq (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) :
    Real.sqrt (lam * mu) = mu * alp lam mu := by
  unfold alp
  have e : lam * mu = mu ^ 2 * (lam / mu) := by field_simp
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hmu.le]

lemma lam_eq (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) : lam = mu * alp lam mu ^ 2 := by
  rw [alp_sq lam mu hlam hmu]; field_simp

lemma coef1 (a s lam mu : ℝ) (ha : a ≠ 0) (hs : s = mu * a) (hl : lam = mu * a ^ 2) (k : ℤ) :
    a ^ k * s = lam * a ^ (k - 1) := by
  subst hs hl
  rw [zpow_sub_one₀ ha]
  field_simp

lemma coef2 (a s mu : ℝ) (ha : a ≠ 0) (hs : s = mu * a) (k : ℤ) :
    a ^ k * s = mu * a ^ (k + 1) := by
  subst hs
  rw [zpow_add_one₀ ha]
  ring

lemma rpow_half_eq (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (m : ℤ) :
    alp lam mu ^ m = (lam / mu) ^ ((m : ℝ) / 2) := by
  unfold alp
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (div_pos hlam hmu).le]
  congr 1
  ring

lemma besselI_deriv_int (m : ℤ) (y : ℝ) :
    HasDerivAt (fun y => besselI m.natAbs y)
      ((besselI (m - 1).natAbs y + besselI (m + 1).natAbs y) / 2) y := by
  rcases Int.eq_nat_or_neg m with ⟨a, rfl | rfl⟩
  · cases a with
    | zero =>
      rw [show ((0 : ℕ) : ℤ).natAbs = 0 by omega, show (((0 : ℕ) : ℤ) - 1).natAbs = 1 by omega,
        show (((0 : ℕ) : ℤ) + 1).natAbs = 1 by omega, add_self_div_two]
      exact besselI_hasDerivAt_zero y
    | succ j =>
      rw [show ((j + 1 : ℕ) : ℤ).natAbs = j + 1 by omega,
        show (((j + 1 : ℕ) : ℤ) - 1).natAbs = j by omega,
        show (((j + 1 : ℕ) : ℤ) + 1).natAbs = j + 2 by omega]
      exact besselI_hasDerivAt_succ j y
  · cases a with
    | zero =>
      rw [show (-((0 : ℕ) : ℤ)).natAbs = 0 by omega, show (-((0 : ℕ) : ℤ) - 1).natAbs = 1 by omega,
        show (-((0 : ℕ) : ℤ) + 1).natAbs = 1 by omega, add_self_div_two]
      exact besselI_hasDerivAt_zero y
    | succ j =>
      rw [show (-((j + 1 : ℕ) : ℤ)).natAbs = j + 1 by omega,
        show (-((j + 1 : ℕ) : ℤ) - 1).natAbs = j + 2 by omega,
        show (-((j + 1 : ℕ) : ℤ) + 1).natAbs = j by omega]
      exact (besselI_hasDerivAt_succ j y).congr_deriv (by ring)

lemma lin_hasDerivAt (c t : ℝ) : HasDerivAt (fun t : ℝ => 2 * t * c) (2 * c) t := by
  have := ((hasDerivAt_id' t).const_mul 2).mul_const c
  simpa using this

/-- integer-order Bessel function along `y = 2t√(λμ)` -/
noncomputable def Jz (lam mu : ℝ) (m : ℤ) (t : ℝ) : ℝ :=
  besselI m.natAbs (2 * t * Real.sqrt (lam * mu))

lemma Jz_deriv (lam mu : ℝ) (m : ℤ) (t : ℝ) :
    HasDerivAt (Jz lam mu m)
      (Real.sqrt (lam * mu) * (Jz lam mu (m - 1) t + Jz lam mu (m + 1) t)) t := by
  have h := (besselI_deriv_int m (2 * t * Real.sqrt (lam * mu))).comp t
    (lin_hasDerivAt (Real.sqrt (lam * mu)) t)
  refine h.congr_deriv ?_
  unfold Jz
  ring

/-- `α^{m+c} I_{|m+d|}(y)`: every such shift solves the three-term system -/
noncomputable def Pz (lam mu : ℝ) (c d m : ℤ) (t : ℝ) : ℝ :=
  alp lam mu ^ (m + c) * Jz lam mu (m + d) t

lemma Pz_deriv (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (c d m : ℤ) (t : ℝ) :
    HasDerivAt (Pz lam mu c d m)
      (lam * Pz lam mu c d (m - 1) t + mu * Pz lam mu c d (m + 1) t) t := by
  have ha := (alp_pos lam mu hlam hmu).ne'
  have hs := sqrt_eq lam mu hlam hmu
  have hl := lam_eq lam mu hlam hmu
  have h := (Jz_deriv lam mu (m + d) t).const_mul (alp lam mu ^ (m + c))
  refine h.congr_deriv ?_
  unfold Pz
  rw [show m - 1 + c = m + c - 1 by ring, show m - 1 + d = m + d - 1 by ring,
    show m + 1 + c = m + c + 1 by ring, show m + 1 + d = m + d + 1 by ring]
  linear_combination Jz lam mu (m + d - 1) t * coef1 _ _ lam mu ha hs hl (m + c)
    + Jz lam mu (m + d + 1) t * coef2 _ _ mu ha hs (m + c)

/-- the tail series `S_N(t) = ∑_j α^{-j} I_{N+j}(y)` -/
noncomputable def SN (lam mu : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, (alp lam mu)⁻¹ ^ j * besselI (N + j) (2 * t * Real.sqrt (lam * mu))

lemma bI_shift_le (N j : ℕ) (y X : ℝ) (hX : |y| / 2 ≤ X) :
    |besselI (N + j) y| ≤ X ^ N * (X ^ j / (j.factorial : ℝ)) * Real.exp (X ^ 2) := by
  have h := besselI_abs_le (N + j) y
  have hX0 : 0 ≤ |y| / 2 := by positivity
  have hj : (0 : ℝ) < j.factorial := by positivity
  have hf : (j.factorial : ℝ) ≤ ((N + j).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_left j N)
  have e1 : (y / 2) ^ 2 ≤ X ^ 2 := by
    rw [← sq_abs, abs_div, abs_two]
    exact pow_le_pow_left₀ hX0 hX 2
  have hX1 : 0 ≤ X := hX0.trans hX
  have hp : (|y| / 2) ^ (N + j) ≤ X ^ (N + j) := pow_le_pow_left₀ hX0 hX _
  have hq1 : (|y| / 2) ^ (N + j) / ((N + j).factorial : ℝ) ≤ (|y| / 2) ^ (N + j) / (j.factorial : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hj hf
  have hq2 : (|y| / 2) ^ (N + j) / (j.factorial : ℝ) ≤ X ^ (N + j) / (j.factorial : ℝ) :=
    div_le_div_of_nonneg_right hp hj.le
  refine h.trans ?_
  calc (|y| / 2) ^ (N + j) / ((N + j).factorial : ℝ) * Real.exp ((y / 2) ^ 2)
      ≤ X ^ (N + j) / (j.factorial : ℝ) * Real.exp (X ^ 2) :=
        mul_le_mul (hq1.trans hq2) (Real.exp_le_exp.2 e1) (Real.exp_pos _).le
          (div_nonneg (pow_nonneg hX1 _) hj.le)
    _ = X ^ N * (X ^ j / (j.factorial : ℝ)) * Real.exp (X ^ 2) := by rw [pow_add]; ring

lemma SN_summable (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (N : ℕ) (t : ℝ) :
    Summable (fun j : ℕ => (alp lam mu)⁻¹ ^ j * besselI (N + j) (2 * t * Real.sqrt (lam * mu))) := by
  set y := 2 * t * Real.sqrt (lam * mu)
  set X := |y| / 2
  have hb : (0 : ℝ) < (alp lam mu)⁻¹ := inv_pos.2 (alp_pos lam mu hlam hmu)
  refine Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial ((alp lam mu)⁻¹ * X)).mul_left (X ^ N * Real.exp (X ^ 2)))
    (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hb]
  calc (alp lam mu)⁻¹ ^ j * |besselI (N + j) y|
      ≤ (alp lam mu)⁻¹ ^ j * (X ^ N * (X ^ j / (j.factorial : ℝ)) * Real.exp (X ^ 2)) :=
        mul_le_mul_of_nonneg_left (bI_shift_le N j y X le_rfl) (by positivity)
    _ = X ^ N * Real.exp (X ^ 2) * (((alp lam mu)⁻¹ * X) ^ j / (j.factorial : ℝ)) := by
        rw [mul_pow]; ring

lemma SN_deriv (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (M : ℕ) (t : ℝ) :
    HasDerivAt (SN lam mu (M + 1))
      (Real.sqrt (lam * mu) * (SN lam mu M t + SN lam mu (M + 2) t)) t := by
  set s := Real.sqrt (lam * mu) with hsdef
  set b := (alp lam mu)⁻¹ with hbdef
  have hb : 0 < b := inv_pos.2 (alp_pos lam mu hlam hmu)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set X : ℝ := (|t| + 1) * s with hX
  have hX0 : 0 ≤ X := by positivity
  have hmem : ∀ z : ℝ, z ∈ Metric.ball (0 : ℝ) (|t| + 1) → |2 * z * s| / 2 ≤ X := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hz
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hs0, hX]
    nlinarith [abs_nonneg z]
  have hterm : ∀ (j : ℕ) (z : ℝ), HasDerivAt (fun z : ℝ => b ^ j * besselI (M + 1 + j) (2 * z * s))
      (b ^ j * (s * (besselI (M + j) (2 * z * s) + besselI (M + 2 + j) (2 * z * s)))) z := by
    intro j z
    have h := (besselI_hasDerivAt_succ (M + j) (2 * z * s)).comp z (lin_hasDerivAt s z)
    rw [show M + 1 + j = M + j + 1 by omega]
    refine (h.const_mul (b ^ j)).congr_deriv ?_
    rw [show M + 2 + j = M + j + 2 by omega]
    ring
  have key : HasDerivAt (fun z : ℝ => ∑' j : ℕ, b ^ j * besselI (M + 1 + j) (2 * z * s))
      (∑' j : ℕ, b ^ j * (s * (besselI (M + j) (2 * t * s) + besselI (M + 2 + j) (2 * t * s)))) t :=
    hasDerivAt_tsum_of_isPreconnected
      (u := fun j : ℕ => s * (X ^ M + X ^ (M + 2)) * Real.exp (X ^ 2) * ((b * X) ^ j / (j.factorial : ℝ)))
      (g := fun (j : ℕ) (z : ℝ) => b ^ j * besselI (M + 1 + j) (2 * z * s))
      (g' := fun (j : ℕ) (z : ℝ) =>
        b ^ j * (s * (besselI (M + j) (2 * z * s) + besselI (M + 2 + j) (2 * z * s))))
      ((Real.summable_pow_div_factorial _).mul_left _) Metric.isOpen_ball
      (convex_ball (0 : ℝ) (|t| + 1)).isPreconnected
      (fun j z _ => hterm j z)
      (fun j z hz => by
        have h1 := bI_shift_le M j (2 * z * s) X (hmem z hz)
        have h2 := bI_shift_le (M + 2) j (2 * z * s) X (hmem z hz)
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos hb, abs_of_nonneg hs0]
        have h3 := abs_add_le (besselI (M + j) (2 * z * s)) (besselI (M + 2 + j) (2 * z * s))
        calc b ^ j * (s * |besselI (M + j) (2 * z * s) + besselI (M + 2 + j) (2 * z * s)|)
            ≤ b ^ j * (s * (X ^ M * (X ^ j / (j.factorial : ℝ)) * Real.exp (X ^ 2)
                + X ^ (M + 2) * (X ^ j / (j.factorial : ℝ)) * Real.exp (X ^ 2))) := by
              gcongr
              exact h3.trans (add_le_add h1 h2)
          _ = s * (X ^ M + X ^ (M + 2)) * Real.exp (X ^ 2) * ((b * X) ^ j / (j.factorial : ℝ)) := by
              rw [mul_pow]; ring)
      (Metric.mem_ball_self (by positivity : (0 : ℝ) < |t| + 1))
      (SN_summable lam mu hlam hmu (M + 1) 0)
      (by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith)
  have hA := SN_summable lam mu hlam hmu M t
  have hB := SN_summable lam mu hlam hmu (M + 2) t
  have hval : (∑' j : ℕ, b ^ j * (s * (besselI (M + j) (2 * t * s) + besselI (M + 2 + j) (2 * t * s))))
      = s * (SN lam mu M t + SN lam mu (M + 2) t) := by
    have e : (fun j : ℕ => b ^ j * (s * (besselI (M + j) (2 * t * s) + besselI (M + 2 + j) (2 * t * s))))
        = fun j : ℕ => s * (b ^ j * besselI (M + j) (2 * t * s))
            + s * (b ^ j * besselI (M + 2 + j) (2 * t * s)) := by
      funext j; ring
    rw [e, (hA.mul_left s).tsum_add (hB.mul_left s), tsum_mul_left, tsum_mul_left, ← mul_add]
    rfl
  rw [hval] at key
  exact key

lemma SN_split (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (N : ℕ) (t : ℝ) :
    SN lam mu (N + 1) t = besselI (N + 1) (2 * t * Real.sqrt (lam * mu))
      + (alp lam mu)⁻¹ * SN lam mu (N + 2) t := by
  have hs := SN_summable lam mu hlam hmu (N + 2) t
  have hs' : Summable (fun j : ℕ => (alp lam mu)⁻¹ ^ (j + 1)
      * besselI (N + 1 + (j + 1)) (2 * t * Real.sqrt (lam * mu))) := by
    have e : (fun j : ℕ => (alp lam mu)⁻¹ ^ (j + 1)
        * besselI (N + 1 + (j + 1)) (2 * t * Real.sqrt (lam * mu))) = fun j : ℕ =>
        (alp lam mu)⁻¹ * ((alp lam mu)⁻¹ ^ j * besselI (N + 2 + j) (2 * t * Real.sqrt (lam * mu))) := by
      funext j; rw [show N + 1 + (j + 1) = N + 2 + j by omega, pow_succ]; ring
    rw [e]; exact hs.mul_left _
  unfold SN
  rw [tsum_eq_zero_add' (f := fun j : ℕ => (alp lam mu)⁻¹ ^ j
    * besselI (N + 1 + j) (2 * t * Real.sqrt (lam * mu))) hs', ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  congr 1
  funext j
  rw [show N + 1 + (j + 1) = N + 2 + j by omega, pow_succ]
  ring

/-- the bracket of (2.75) at state `n` -/
noncomputable def Fb (lam mu : ℝ) (i n : ℕ) (t : ℝ) : ℝ :=
  Pz lam mu (-(i : ℤ)) (-(i : ℤ)) n t + Pz lam mu (-(i : ℤ) - 1) ((i : ℤ) + 1) n t
    + (1 - lam / mu) * (alp lam mu ^ ((n : ℤ) - i - 2) * SN lam mu (n + i + 2) t)

/-- the reflected bracket at state `-1` -/
noncomputable def Fm1 (lam mu : ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  Pz lam mu (-(i : ℤ)) (-(i : ℤ)) (-1) t + Pz lam mu (-(i : ℤ) - 1) ((i : ℤ) + 1) (-1) t
    + (1 - lam / mu) * (alp lam mu ^ (-(i : ℤ) - 3) * SN lam mu (i + 1) t)

lemma Cpart_deriv (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) (t : ℝ) :
    HasDerivAt (fun t => alp lam mu ^ ((n : ℤ) - i - 2) * SN lam mu (n + i + 2) t)
      (lam * (alp lam mu ^ ((n : ℤ) - i - 3) * SN lam mu (n + i + 1) t)
        + mu * (alp lam mu ^ ((n : ℤ) - i - 1) * SN lam mu (n + i + 3) t)) t := by
  have ha := (alp_pos lam mu hlam hmu).ne'
  have hs := sqrt_eq lam mu hlam hmu
  have hl := lam_eq lam mu hlam hmu
  have h := (SN_deriv lam mu hlam hmu (n + i + 1) t).const_mul (alp lam mu ^ ((n : ℤ) - i - 2))
  refine h.congr_deriv ?_
  rw [show (n : ℤ) - i - 3 = (n : ℤ) - i - 2 - 1 by ring,
    show (n : ℤ) - i - 1 = (n : ℤ) - i - 2 + 1 by ring,
    show n + i + 1 + 2 = n + i + 3 by omega]
  linear_combination SN lam mu (n + i + 1) t * coef1 _ _ lam mu ha hs hl ((n : ℤ) - i - 2)
    + SN lam mu (n + i + 3) t * coef2 _ _ mu ha hs ((n : ℤ) - i - 2)

lemma Fb_deriv_succ (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i k : ℕ) (t : ℝ) :
    HasDerivAt (Fb lam mu i (k + 1)) (lam * Fb lam mu i k t + mu * Fb lam mu i (k + 2) t) t := by
  have hA := Pz_deriv lam mu hlam hmu (-(i : ℤ)) (-(i : ℤ)) ((k + 1 : ℕ) : ℤ) t
  have hB := Pz_deriv lam mu hlam hmu (-(i : ℤ) - 1) ((i : ℤ) + 1) ((k + 1 : ℕ) : ℤ) t
  have hC := Cpart_deriv lam mu hlam hmu i (k + 1) t
  have h := (hA.add hB).add (hC.const_mul (1 - lam / mu))
  refine h.congr_deriv ?_
  unfold Fb
  rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring,
    show ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) by push_cast; ring,
    show ((k + 1 : ℕ) : ℤ) - i - 3 = (k : ℤ) - i - 2 by push_cast; ring,
    show ((k + 1 : ℕ) : ℤ) - i - 1 = ((k + 2 : ℕ) : ℤ) - i - 2 by push_cast; ring,
    show k + 1 + i + 1 = k + i + 2 by omega, show k + 1 + i + 3 = k + 2 + i + 2 by omega]
  ring

lemma Fb_deriv_zero (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ) (t : ℝ) :
    HasDerivAt (Fb lam mu i 0) (lam * Fm1 lam mu i t + mu * Fb lam mu i 1 t) t := by
  have hA := Pz_deriv lam mu hlam hmu (-(i : ℤ)) (-(i : ℤ)) ((0 : ℕ) : ℤ) t
  have hB := Pz_deriv lam mu hlam hmu (-(i : ℤ) - 1) ((i : ℤ) + 1) ((0 : ℕ) : ℤ) t
  have hC := Cpart_deriv lam mu hlam hmu i 0 t
  have h := (hA.add hB).add (hC.const_mul (1 - lam / mu))
  refine h.congr_deriv ?_
  unfold Fb Fm1
  rw [show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num,
    show ((0 : ℕ) : ℤ) + 1 = ((1 : ℕ) : ℤ) by norm_num,
    show ((0 : ℕ) : ℤ) - i - 3 = -(i : ℤ) - 3 by push_cast; ring,
    show ((0 : ℕ) : ℤ) - i - 1 = ((1 : ℕ) : ℤ) - i - 2 by push_cast; ring,
    show 0 + i + 1 = i + 1 by omega, show 0 + i + 3 = 1 + i + 2 by omega]
  ring

lemma reflection (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ) (t : ℝ) :
    lam * Fm1 lam mu i t = mu * Fb lam mu i 0 t := by
  have ha := (alp_pos lam mu hlam hmu).ne'
  have hl := lam_eq lam mu hlam hmu
  have hr := alp_sq lam mu hlam hmu
  unfold Fm1 Fb Pz Jz
  rw [SN_split lam mu hlam hmu i t]
  rw [show (-1 + -(i : ℤ)).natAbs = i + 1 by omega, show (-1 + ((i : ℤ) + 1)).natAbs = i by omega,
    show (((0 : ℕ) : ℤ) + -(i : ℤ)).natAbs = i by omega,
    show (((0 : ℕ) : ℤ) + ((i : ℤ) + 1)).natAbs = i + 1 by omega,
    show 0 + i + 2 = i + 2 by omega]
  rw [show (-1 + -(i : ℤ)) = -(i : ℤ) + (-1) by ring,
    show (-1 + (-(i : ℤ) - 1)) = -(i : ℤ) + (-2) by ring,
    show (-(i : ℤ) - 3) = -(i : ℤ) + (-3) by ring,
    show (((0 : ℕ) : ℤ) + -(i : ℤ)) = -(i : ℤ) + 0 by push_cast; ring,
    show (((0 : ℕ) : ℤ) + (-(i : ℤ) - 1)) = -(i : ℤ) + (-1) by push_cast; ring,
    show (((0 : ℕ) : ℤ) - (i : ℤ) - 2) = -(i : ℤ) + (-2) by push_cast; ring]
  simp only [zpow_add₀ ha, zpow_neg, zpow_zero, zpow_one]
  rw [← hr]
  generalize alp lam mu ^ (i : ℤ) = W
  generalize besselI i (2 * t * Real.sqrt (lam * mu)) = X
  generalize besselI (i + 1) (2 * t * Real.sqrt (lam * mu)) = Y
  generalize SN lam mu (i + 2) t = Z
  generalize alp lam mu = a at ha hl ⊢
  subst hl
  field_simp
  ring


lemma term_eq (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n j : ℕ) (t : ℝ) :
    (lam / mu) ^ (-(((j + n + i + 2 : ℕ) : ℝ)) / 2) * besselI (j + n + i + 2) (2 * t * Real.sqrt (lam * mu))
      = alp lam mu ^ (-((n + i + 2 : ℕ) : ℤ)) *
          ((alp lam mu)⁻¹ ^ j * besselI (n + i + 2 + j) (2 * t * Real.sqrt (lam * mu))) := by
  have ha := (alp_pos lam mu hlam hmu).ne'
  rw [show j + n + i + 2 = n + i + 2 + j by omega]
  have e : (-(((n + i + 2 + j : ℕ) : ℝ)) / 2) = (((-((n + i + 2 + j : ℕ) : ℤ)) : ℤ) : ℝ) / 2 := by
    push_cast; ring
  rw [e, ← rpow_half_eq lam mu hlam hmu, inv_pow, ← zpow_natCast (alp lam mu) j, ← zpow_neg,
    ← mul_assoc, ← zpow_add₀ ha]
  congr 1
  congr 1
  push_cast
  ring

/-- T2 -/
theorem mm1_tail_summable (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ) :
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
        Summable (fun j : ℕ => (lam / mu) ^ (-(((j + n + i + 2 : ℕ) : ℝ)) / 2)
          * besselI (j + n + i + 2) (2 * t * Real.sqrt (lam * mu))) := by
  intro n t _
  simp_rw [term_eq lam mu hlam hmu i n _ t]
  exact (SN_summable lam mu hlam hmu (n + i + 2) t).mul_left _

lemma claim1 (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) (t : ℝ) :
    mm1Transient lam mu i n t = Real.exp (-(lam + mu) * t) * Fb lam mu i n t := by
  have ha := (alp_pos lam mu hlam hmu).ne'
  have hA : (lam / mu) ^ (((n : ℝ) - (i : ℝ)) / 2)
      * besselIZ ((n : ℤ) - (i : ℤ)) (2 * t * Real.sqrt (lam * mu))
      = Pz lam mu (-(i : ℤ)) (-(i : ℤ)) n t := by
    rw [show ((n : ℝ) - (i : ℝ)) = ((((n : ℤ) + -(i : ℤ)) : ℤ) : ℝ) by push_cast; ring,
      ← rpow_half_eq lam mu hlam hmu]
    unfold Pz Jz besselIZ
    congr 1
    all_goals omega
  have hB : (lam / mu) ^ (((n : ℝ) - (i : ℝ) - 1) / 2)
      * besselI (n + i + 1) (2 * t * Real.sqrt (lam * mu))
      = Pz lam mu (-(i : ℤ) - 1) ((i : ℤ) + 1) n t := by
    rw [show ((n : ℝ) - (i : ℝ) - 1) = ((((n : ℤ) + (-(i : ℤ) - 1)) : ℤ) : ℝ) by push_cast; ring,
      ← rpow_half_eq lam mu hlam hmu]
    unfold Pz Jz
    congr 1
    all_goals omega
  have hC : (1 - lam / mu) * (lam / mu) ^ n *
      ∑' j : ℕ, (lam / mu) ^ (-(((j + n + i + 2 : ℕ) : ℝ)) / 2)
        * besselI (j + n + i + 2) (2 * t * Real.sqrt (lam * mu))
      = (1 - lam / mu) * (alp lam mu ^ ((n : ℤ) - i - 2) * SN lam mu (n + i + 2) t) := by
    simp_rw [term_eq lam mu hlam hmu i n _ t]
    rw [mul_assoc]
    congr 1
    rw [tsum_mul_left, ← mul_assoc]
    unfold SN
    congr 1
    rw [← alp_sq lam mu hlam hmu, ← pow_mul, ← zpow_natCast, ← zpow_add₀ ha]
    congr 1
    push_cast
    ring
  simp only [mm1Transient]
  unfold Fb
  linear_combination Real.exp (-(lam + mu) * t) * (hA + hB + hC)

/-- T3 -/
theorem mm1Transient_isForwardSolution (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ) :
    IsForwardSolution (mm1RHS lam mu) (fun n t => mm1Transient lam mu i n t) := by
  intro n t _
  simp_rw [claim1 lam mu hlam hmu i]
  have h1 : HasDerivAt (fun t : ℝ => -(lam + mu) * t) (-(lam + mu)) t := by
    simpa using (hasDerivAt_id t).const_mul (-(lam + mu))
  cases n with
  | zero =>
    have h := (h1.exp.mul (Fb_deriv_zero lam mu hlam hmu i t)).hasDerivWithinAt (s := Set.Ici (0 : ℝ))
    refine h.congr_deriv ?_
    simp only [mm1RHS]
    linear_combination Real.exp (-(lam + mu) * t) * reflection lam mu hlam hmu i t
  | succ k =>
    have h := (h1.exp.mul (Fb_deriv_succ lam mu hlam hmu i k t)).hasDerivWithinAt
      (s := Set.Ici (0 : ℝ))
    refine h.congr_deriv ?_
    simp only [mm1RHS]
    ring

/-- T4(a) -/
theorem mm1Transient_init (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ) :
    ∀ n : ℕ, mm1Transient lam mu i n 0 = if n = i then 1 else 0 := by
  intro n
  have c1 : (((n : ℤ) + -(i : ℤ)).natAbs = 0) ↔ n = i := by omega
  have c2 : ¬ (((n : ℤ) + ((i : ℤ) + 1)).natAbs = 0) := by omega
  have c3 : ∀ j : ℕ, ¬ (n + i + 2 + j = 0) := fun j => by omega
  rw [claim1 lam mu hlam hmu i n 0]
  simp only [Fb, Pz, Jz, SN, mul_zero, zero_mul, besselI_zero, c1, c2, c3, if_false, tsum_zero,
    add_zero, Real.exp_zero, one_mul]
  split_ifs with h
  · subst h; simp
  · simp


lemma kappa_ge (a : ℝ) (ha : 0 < a) : a ≤ a + a⁻¹ ∧ a⁻¹ ≤ a + a⁻¹ ∧ 1 ≤ a + a⁻¹ := by
  have hi : 0 < a⁻¹ := inv_pos.2 ha
  have hm : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith [sq_nonneg (a - a⁻¹)]

lemma zbound (a : ℝ) (ha : 0 < a) (e : ℤ) : a ^ e ≤ (a + a⁻¹) ^ e.natAbs := by
  obtain ⟨h1, h2, _⟩ := kappa_ge a ha
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · rw [zpow_natCast, show ((k : ℤ)).natAbs = k by omega]
    exact pow_le_pow_left₀ ha.le h1 k
  · rw [zpow_neg, zpow_natCast, ← inv_pow, show (-(k : ℤ)).natAbs = k by omega]
    exact pow_le_pow_left₀ (inv_pos.2 ha).le h2 k

lemma Ibound (K : ℕ) (y X : ℝ) (hX : |y| / 2 ≤ X) :
    |besselI K y| ≤ X ^ K / (K.factorial : ℝ) * Real.exp (X ^ 2) := by
  have h := besselI_abs_le K y
  have hX0 : 0 ≤ |y| / 2 := by positivity
  have hp : (|y| / 2) ^ K ≤ X ^ K := pow_le_pow_left₀ hX0 hX K
  have e1 : (y / 2) ^ 2 ≤ X ^ 2 := by
    rw [← sq_abs, abs_div, abs_two]
    exact pow_le_pow_left₀ hX0 hX 2
  refine h.trans (mul_le_mul (div_le_div_of_nonneg_right hp (by positivity))
    (Real.exp_le_exp.2 e1) (Real.exp_pos _).le (div_nonneg (pow_nonneg (hX0.trans hX) _) (by positivity)))

lemma Gbound (a : ℝ) (ha : 0 < a) (m : ℤ) (y X : ℝ) (hX : |y| / 2 ≤ X) :
    |a ^ m * besselI m.natAbs y| ≤ Real.exp ((a + a⁻¹) * X) * Real.exp (X ^ 2) := by
  have hX0 : 0 ≤ X := (by positivity : (0 : ℝ) ≤ |y| / 2).trans hX
  have hk := (kappa_ge a ha).2.2
  rw [abs_mul, abs_of_pos (zpow_pos ha m)]
  calc a ^ m * |besselI m.natAbs y|
      ≤ (a + a⁻¹) ^ m.natAbs * (X ^ m.natAbs / (m.natAbs.factorial : ℝ) * Real.exp (X ^ 2)) :=
        mul_le_mul (zbound a ha m) (Ibound _ y X hX) (abs_nonneg _) (pow_nonneg (by linarith) _)
    _ = ((a + a⁻¹) * X) ^ m.natAbs / (m.natAbs.factorial : ℝ) * Real.exp (X ^ 2) := by
        rw [mul_pow]; ring
    _ ≤ Real.exp ((a + a⁻¹) * X) * Real.exp (X ^ 2) :=
        mul_le_mul_of_nonneg_right
          (Real.pow_div_factorial_le_exp _ (mul_nonneg (by linarith) hX0) _)
          (Real.exp_pos _).le

lemma tail_bound (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) (t X : ℝ)
    (hX : |2 * t * Real.sqrt (lam * mu)| / 2 ≤ X) :
    |alp lam mu ^ ((n : ℤ) - i - 2) * SN lam mu (n + i + 2) t|
      ≤ Real.exp ((alp lam mu + (alp lam mu)⁻¹) * X) * Real.exp (X ^ 2) := by
  set a := alp lam mu with hadef
  have ha : 0 < a := alp_pos lam mu hlam hmu
  set κ := a + a⁻¹ with hκ
  have hk1 := (kappa_ge a ha).2.2
  have hX0 : 0 ≤ X := (by positivity : (0 : ℝ) ≤ |2 * t * Real.sqrt (lam * mu)| / 2).trans hX
  set y := 2 * t * Real.sqrt (lam * mu) with hy
  set N := n + i + 2 with hN
  set h : ℕ → ℝ := fun k => (κ * X) ^ k / (k.factorial : ℝ) * Real.exp (X ^ 2) with hh
  have hhs : Summable h := (Real.summable_pow_div_factorial _).mul_right _
  have hh0 : ∀ k, 0 ≤ h k := fun k => by
    simp only [hh]; have : 0 ≤ κ * X := mul_nonneg (by linarith) hX0
    positivity
  have hhsum : HasSum h (Real.exp (κ * X) * Real.exp (X ^ 2)) := (exp_hasSum _).mul_right _
  have hS := SN_summable lam mu hlam hmu N t
  have hterm : ∀ j : ℕ, ‖a ^ ((n : ℤ) - i - 2) * (a⁻¹ ^ j * besselI (N + j) y)‖ ≤ h (N + j) := by
    intro j
    have e : a ^ ((n : ℤ) - i - 2) * (a⁻¹ ^ j * besselI (N + j) y)
        = a ^ ((n : ℤ) - i - 2 - j) * besselI (N + j) y := by
      rw [← mul_assoc, inv_pow, ← zpow_natCast a j, ← zpow_neg, ← zpow_add₀ ha.ne']
      congr 2
    rw [e, Real.norm_eq_abs, abs_mul, abs_of_pos (zpow_pos ha _)]
    have hz : a ^ ((n : ℤ) - i - 2 - j) ≤ κ ^ (N + j) :=
      (zbound a ha _).trans (pow_le_pow_right₀ hk1 (by omega))
    calc a ^ ((n : ℤ) - i - 2 - j) * |besselI (N + j) y|
        ≤ κ ^ (N + j) * (X ^ (N + j) / ((N + j).factorial : ℝ) * Real.exp (X ^ 2)) :=
          mul_le_mul hz (Ibound _ y X hX) (abs_nonneg _) (pow_nonneg (by linarith) _)
      _ = h (N + j) := by simp only [hh]; rw [mul_pow]; ring
  have hcomp : Summable (fun j : ℕ => h (N + j)) := hhs.comp_injective (add_right_injective N)
  have hsn : Summable (fun j : ℕ => ‖a ^ ((n : ℤ) - i - 2) * (a⁻¹ ^ j * besselI (N + j) y)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hterm hcomp
  have hinj := tsum_comp_le_tsum_of_inj hhs hh0 (add_right_injective N)
  unfold SN
  rw [← tsum_mul_left, ← Real.norm_eq_abs]
  calc ‖∑' j : ℕ, a ^ ((n : ℤ) - i - 2) * (a⁻¹ ^ j * besselI (N + j) y)‖
      ≤ ∑' j : ℕ, ‖a ^ ((n : ℤ) - i - 2) * (a⁻¹ ^ j * besselI (N + j) y)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' j : ℕ, h (N + j) := hasSum_le hterm hsn.hasSum hcomp.hasSum
    _ ≤ ∑' k, h k := hinj
    _ = Real.exp (κ * X) * Real.exp (X ^ 2) := hhsum.tsum_eq

/-- T4(b) -/
theorem mm1Transient_bdd (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ) :
    ∀ T : ℝ, ∃ C : ℝ, ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T, |mm1Transient lam mu i n t| ≤ C := by
  intro T
  set a := alp lam mu with hadef
  have ha : 0 < a := alp_pos lam mu hlam hmu
  set s := Real.sqrt (lam * mu) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set X := |T| * s with hX
  set G := Real.exp ((a + a⁻¹) * X) * Real.exp (X ^ 2) with hG
  refine ⟨G + a ^ (-2 * (i : ℤ) - 2) * G + |1 - lam / mu| * G, fun n t ht => ?_⟩
  have hXt : |2 * t * s| / 2 ≤ X := by
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hs0, abs_of_nonneg ht.1, hX]
    have : t ≤ |T| := ht.2.trans (le_abs_self T)
    nlinarith
  have hG0 : 0 ≤ G := by positivity
  rw [claim1 lam mu hlam hmu i n t, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hE : Real.exp (-(lam + mu) * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
  have hA : |Pz lam mu (-(i : ℤ)) (-(i : ℤ)) n t| ≤ G := by
    unfold Pz Jz
    exact Gbound a ha _ _ X hXt
  have hB : |Pz lam mu (-(i : ℤ) - 1) ((i : ℤ) + 1) n t| ≤ a ^ (-2 * (i : ℤ) - 2) * G := by
    unfold Pz Jz
    rw [show (n : ℤ) + (-(i : ℤ) - 1) = (-2 * (i : ℤ) - 2) + ((n : ℤ) + ((i : ℤ) + 1)) by ring,
      zpow_add₀ ha.ne', mul_assoc, abs_mul, abs_of_pos (zpow_pos ha _)]
    exact mul_le_mul_of_nonneg_left (Gbound a ha _ _ X hXt) (zpow_pos ha _).le
  have hC := tail_bound lam mu hlam hmu i n t X hXt
  have hF : |Fb lam mu i n t| ≤ G + a ^ (-2 * (i : ℤ) - 2) * G + |1 - lam / mu| * G := by
    unfold Fb
    calc _ ≤ |Pz lam mu (-(i : ℤ)) (-(i : ℤ)) n t| + |Pz lam mu (-(i : ℤ) - 1) ((i : ℤ) + 1) n t|
          + |1 - lam / mu| * |alp lam mu ^ ((n : ℤ) - i - 2) * SN lam mu (n + i + 2) t| := by
          rw [← abs_mul]; exact abs_add_three _ _ _
      _ ≤ _ := by gcongr
  have hF0 : 0 ≤ |Fb lam mu i n t| := abs_nonneg _
  calc Real.exp (-(lam + mu) * t) * |Fb lam mu i n t| ≤ 1 * |Fb lam mu i n t| :=
        mul_le_mul_of_nonneg_right hE hF0
    _ ≤ _ := by rw [one_mul]; exact hF

/-- T4 as in the plan -/
theorem mm1Transient_init_bdd (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ) :
    (∀ n : ℕ, mm1Transient lam mu i n 0 = if n = i then 1 else 0) ∧
      ∀ T : ℝ, ∃ C : ℝ, ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T, |mm1Transient lam mu i n t| ≤ C :=
  ⟨mm1Transient_init lam mu hlam hmu i, mm1Transient_bdd lam mu hlam hmu i⟩

end MM1Aux12395959

namespace MM1Aux12395959
open QueueingFundamentals.Transient

lemma rhs_sub (lam mu : ℝ) (p q : ℕ → ℝ) (n : ℕ) :
    mm1RHS lam mu (fun m => p m - q m) n = mm1RHS lam mu p n - mm1RHS lam mu q n := by
  cases n <;> simp only [mm1RHS] <;> ring

lemma rhs_bound (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (d : ℕ → ℝ) (B : ℝ)
    (hB : ∀ m, |d m| ≤ B) (n : ℕ) :
    |mm1RHS lam mu d n| ≤ 2 * (lam + mu) * B := by
  have h0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  cases n with
  | zero =>
    simp only [mm1RHS]
    calc |-lam * d 0 + mu * d 1| ≤ |-lam * d 0| + |mu * d 1| := abs_add_le _ _
      _ = lam * |d 0| + mu * |d 1| := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_pos hlam, abs_of_pos hmu]
      _ ≤ lam * B + mu * B := by gcongr <;> exact hB _
      _ ≤ 2 * (lam + mu) * B := by nlinarith
  | succ n =>
    simp only [mm1RHS]
    calc |-(lam + mu) * d (n + 1) + lam * d n + mu * d (n + 2)|
        ≤ |-(lam + mu) * d (n + 1)| + |lam * d n| + |mu * d (n + 2)| := abs_add_three _ _ _
      _ = (lam + mu) * |d (n + 1)| + lam * |d n| + mu * |d (n + 2)| := by
          rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < lam + mu),
            abs_of_pos hlam, abs_of_pos hmu]
      _ ≤ (lam + mu) * B + lam * B + mu * B := by gcongr <;> exact hB _
      _ = 2 * (lam + mu) * B := by ring

lemma zero_sol (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (d : ℕ → ℝ → ℝ)
    (hd : IsForwardSolution (mm1RHS lam mu) d) (h0 : ∀ n, d n 0 = 0)
    (hb : ∀ T : ℝ, ∃ C : ℝ, ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T, |d n t| ≤ C) :
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → d n t = 0 := by
  intro n t ht
  obtain ⟨C, hC⟩ := hb t
  set c : ℝ := 2 * (lam + mu) with hc
  have key : ∀ k : ℕ, ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) t,
      |d n s| ≤ C * (c * s) ^ k / (k.factorial : ℝ) := by
    intro k
    induction k with
    | zero => intro n s hs; simpa using hC n s hs
    | succ k ih =>
      intro n s hs
      have hcont : ContinuousOn (d n) (Set.Icc 0 s) := fun x hx =>
        ((hd n x hx.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
      have hBd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => C * (c * x) ^ (k + 1) / ((k + 1).factorial : ℝ))
          (c * (C * (c * x) ^ k / (k.factorial : ℝ))) x := by
        intro x
        have h1 : HasDerivAt (fun x : ℝ => C * (c * x) ^ (k + 1) / ((k + 1).factorial : ℝ))
            (C * (((k + 1 : ℕ) : ℝ) * (c * x) ^ (k + 1 - 1) * (c * 1)) / ((k + 1).factorial : ℝ))
            x :=
          ((((hasDerivAt_id x).const_mul c).pow (k + 1)).const_mul C).div_const _
        refine h1.congr_deriv ?_
        have hk : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
          push_cast [Nat.factorial_succ]; ring
        rw [hk, Nat.add_sub_cancel]
        have : (k.factorial : ℝ) ≠ 0 := by positivity
        field_simp
        push_cast
        ring
      have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := d n) (a := 0) (b := s)
        (f' := fun x => mm1RHS lam mu (fun m => d m x) n)
        (B := fun x : ℝ => C * (c * x) ^ (k + 1) / ((k + 1).factorial : ℝ))
        (B' := fun x : ℝ => c * (C * (c * x) ^ k / (k.factorial : ℝ)))
        hcont
        (fun x hx => (hd n x hx.1).mono (Set.Ici_subset_Ici.2 hx.1))
        (by simp [h0])
        hBd
        (fun x hx => by
          rw [Real.norm_eq_abs]
          exact rhs_bound lam mu hlam hmu _ _
            (fun m => ih m x ⟨hx.1, le_trans hx.2.le hs.2⟩) n)
        (Set.right_mem_Icc.2 hs.1)
      simpa [Real.norm_eq_abs] using this
  have hlim : Filter.Tendsto (fun k : ℕ => C * ((c * t) ^ k / (k.factorial : ℝ)))
      Filter.atTop (nhds (C * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (c * t)).const_mul C
  rw [mul_zero] at hlim
  have hle : |d n t| ≤ 0 := ge_of_tendsto' hlim (fun k => by
    have := key k n t ⟨ht, le_rfl⟩
    rw [mul_div_assoc] at this
    exact this)
  exact abs_nonpos_iff.1 hle

/-- T5: uniqueness of locally bounded solutions of (2.72). -/
theorem mm1_forward_unique (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (p q : ℕ → ℝ → ℝ)
    (hp : IsForwardSolution (mm1RHS lam mu) p) (hq : IsForwardSolution (mm1RHS lam mu) q)
    (h0 : ∀ n, p n 0 = q n 0)
    (hpb : ∀ T : ℝ, ∃ C : ℝ, ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T, |p n t| ≤ C)
    (hqb : ∀ T : ℝ, ∃ C : ℝ, ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T, |q n t| ≤ C) :
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → p n t = q n t := by
  have hd : IsForwardSolution (mm1RHS lam mu) (fun n t => p n t - q n t) := by
    intro n t ht
    rw [rhs_sub]
    exact (hp n t ht).sub (hq n t ht)
  have hz := zero_sol lam mu hlam hmu (fun n t => p n t - q n t) hd
    (fun n => by simp [h0 n])
    (fun T => by
      obtain ⟨C1, h1⟩ := hpb T
      obtain ⟨C2, h2⟩ := hqb T
      exact ⟨C1 + C2, fun n t htT => (abs_sub _ _).trans (add_le_add (h1 n t htT) (h2 n t htT))⟩)
  intro n t ht
  exact sub_eq_zero.1 (hz n t ht)

end MM1Aux12395959

namespace MM1Aux12395959
open QueueingFundamentals.Transient

/-- `(lam+mu)` times one step of the uniformized M/M/1 kernel, acting on row vectors. -/
def stepS (lam mu : ℝ) (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => mu * a 0 + mu * a 1
  | n + 1 => lam * a n + mu * a (n + 2)

/-- `kerA k = δ_i S^k` (unnormalized: total mass `(lam+mu)^k`). -/
def kerA (lam mu : ℝ) (i : ℕ) : ℕ → ℕ → ℝ
  | 0 => fun n => if n = i then 1 else 0
  | k + 1 => stepS lam mu (kerA lam mu i k)

lemma stepS_nonneg (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (n : ℕ) : 0 ≤ stepS lam mu a n := by
  cases n with
  | zero => exact add_nonneg (mul_nonneg hmu.le (ha 0)) (mul_nonneg hmu.le (ha 1))
  | succ n => exact add_nonneg (mul_nonneg hlam.le (ha n)) (mul_nonneg hmu.le (ha (n + 2)))

lemma stepS_hasSum (lam mu : ℝ) (a : ℕ → ℝ) (s : ℝ) (ha : HasSum a s) :
    HasSum (stepS lam mu a) ((lam + mu) * s) := by
  have h1 : HasSum (fun n => a (n + 1)) (s - a 0) := by
    have := (hasSum_nat_add_iff' 1).mpr ha
    simpa using this
  have h2 : HasSum (fun n : ℕ => if n = 0 then (0 : ℝ) else a (n - 1)) s := by
    rw [← hasSum_nat_add_iff' 1]
    simpa using ha
  have h3 : HasSum (fun n : ℕ => if n = 0 then a 0 else 0) (a 0) := hasSum_ite_eq 0 (a 0)
  have := ((h1.mul_left mu).add (h2.mul_left lam)).add (h3.mul_left mu)
  have e : stepS lam mu a = fun b => (mu * a (b + 1) + lam * (if b = 0 then 0 else a (b - 1)))
      + mu * (if b = 0 then a 0 else 0) := by
    funext n
    cases n with
    | zero => (simp [stepS]) <;> ring
    | succ n => (simp [stepS]) <;> ring
  rw [e, show (lam + mu) * s = mu * (s - a 0) + lam * s + mu * a 0 by ring]
  exact this

lemma kerA_nonneg (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ) :
    ∀ k n, 0 ≤ kerA lam mu i k n := by
  intro k
  induction k with
  | zero => intro n; simp only [kerA]; split_ifs <;> norm_num
  | succ k ih => intro n; exact stepS_nonneg lam mu hlam hmu _ ih n

lemma kerA_hasSum (lam mu : ℝ) (i : ℕ) :
    ∀ k, HasSum (kerA lam mu i k) ((lam + mu) ^ k) := by
  intro k
  induction k with
  | zero => simpa [kerA] using hasSum_ite_eq i (1 : ℝ)
  | succ k ih =>
    rw [pow_succ, mul_comm]
    exact stepS_hasSum lam mu _ _ ih

lemma kerA_le (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i k n : ℕ) :
    kerA lam mu i k n ≤ (lam + mu) ^ k :=
  le_hasSum (kerA_hasSum lam mu i k) n (fun m _ => kerA_nonneg lam mu hlam hmu i k m)

/-- the uniformization series without the exponential factor -/
noncomputable def Vser (lam mu : ℝ) (i n : ℕ) (t : ℝ) : ℝ :=
  ∑' k : ℕ, t ^ k / (k.factorial : ℝ) * kerA lam mu i k n

lemma coef_summable (lam mu : ℝ) (t : ℝ) (b : ℕ → ℝ) (C : ℝ)
    (hb : ∀ k, |b k| ≤ C * (lam + mu) ^ k) :
    Summable (fun k : ℕ => t ^ k / (k.factorial : ℝ) * b k) := by
  refine Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial ((lam + mu) * |t|)).mul_left C) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
  have hf : (0 : ℝ) < k.factorial := by positivity
  calc |t| ^ k / (k.factorial : ℝ) * |b k| ≤ |t| ^ k / (k.factorial : ℝ) * (C * (lam + mu) ^ k) :=
        mul_le_mul_of_nonneg_left (hb k) (by positivity)
    _ = C * (((lam + mu) * |t|) ^ k / (k.factorial : ℝ)) := by rw [mul_pow]; ring

lemma Vser_summable (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) (t : ℝ) :
    Summable (fun k : ℕ => t ^ k / (k.factorial : ℝ) * kerA lam mu i k n) :=
  coef_summable lam mu t _ 1 (fun k => by
    rw [abs_of_nonneg (kerA_nonneg lam mu hlam hmu i k n), one_mul]
    exact kerA_le lam mu hlam hmu i k n)

lemma Vser_shift_summable (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) (t : ℝ) :
    Summable (fun k : ℕ => t ^ k / (k.factorial : ℝ) * kerA lam mu i (k + 1) n) :=
  coef_summable lam mu t _ (lam + mu) (fun k => by
    rw [abs_of_nonneg (kerA_nonneg lam mu hlam hmu i (k + 1) n), ← pow_succ']
    exact kerA_le lam mu hlam hmu i (k + 1) n)

lemma aux_pow (R : ℝ) (hR : 1 ≤ R) (k : ℕ) : (k : ℝ) * R ^ (k - 1) ≤ 2 ^ k * R ^ k := by
  cases k with
  | zero => simp
  | succ m =>
    rw [Nat.add_sub_cancel]
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) (m + 1)
    have h1 : ((m + 1 : ℕ) : ℝ) ≤ 2 ^ (m + 1) := by
      push_cast at hb ⊢
      norm_num at hb
      linarith
    calc ((m + 1 : ℕ) : ℝ) * R ^ m ≤ 2 ^ (m + 1) * R ^ m :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 2 ^ (m + 1) * R ^ (m + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (Nat.le_succ m)) (by positivity)

lemma deriv_bound (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (k : ℕ) (z : ℝ) (hz' : |z| ≤ R) :
    ‖(k : ℝ) * z ^ (k - 1) / (k.factorial : ℝ) * kerA lam mu i k n‖
      ≤ (2 * R * (lam + mu)) ^ k / (k.factorial : ℝ) := by
  have hA := kerA_le lam mu hlam hmu i k n
  have hA0 := kerA_nonneg lam mu hlam hmu i k n
  have hf : (0 : ℝ) < k.factorial := by positivity
  have hp : |z| ^ (k - 1) ≤ R ^ (k - 1) := pow_le_pow_left₀ (abs_nonneg z) hz' _
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_pow, Nat.abs_cast, Nat.abs_cast,
    abs_of_nonneg hA0]
  calc (k : ℝ) * |z| ^ (k - 1) / (k.factorial : ℝ) * kerA lam mu i k n
      ≤ (k : ℝ) * R ^ (k - 1) / (k.factorial : ℝ) * (lam + mu) ^ k := by
        apply mul_le_mul _ hA hA0 (by positivity)
        apply div_le_div_of_nonneg_right _ hf.le
        exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg k)
    _ ≤ 2 ^ k * R ^ k / (k.factorial : ℝ) * (lam + mu) ^ k := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right (aux_pow R hR k) hf.le
    _ = (2 * R * (lam + mu)) ^ k / (k.factorial : ℝ) := by rw [mul_pow, mul_pow]; ring

lemma Vser_hasDerivAt0 (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) (t : ℝ) :
    HasDerivAt (fun z : ℝ => ∑' k : ℕ, z ^ k / (k.factorial : ℝ) * kerA lam mu i k n)
      (∑' k : ℕ, (k : ℝ) * t ^ (k - 1) / (k.factorial : ℝ) * kerA lam mu i k n) t := by
  have hR : 1 ≤ |t| + 1 := by have := abs_nonneg t; linarith
  have hmem : ∀ z : ℝ, z ∈ Metric.ball (0 : ℝ) (|t| + 1) → |z| ≤ |t| + 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hz
    exact hz.le
  exact hasDerivAt_tsum_of_isPreconnected
    (u := fun k : ℕ => (2 * (|t| + 1) * (lam + mu)) ^ k / (k.factorial : ℝ))
    (g := fun (k : ℕ) (z : ℝ) => z ^ k / (k.factorial : ℝ) * kerA lam mu i k n)
    (g' := fun (k : ℕ) (z : ℝ) => (k : ℝ) * z ^ (k - 1) / (k.factorial : ℝ) * kerA lam mu i k n)
    (Real.summable_pow_div_factorial _) Metric.isOpen_ball
    (convex_ball (0 : ℝ) (|t| + 1)).isPreconnected
    (fun k z _ => ((hasDerivAt_pow k z).div_const _).mul_const _)
    (fun k z hz => deriv_bound lam mu hlam hmu i n _ hR k z (hmem z hz))
    (Metric.mem_ball_self (by linarith : (0 : ℝ) < |t| + 1))
    (Vser_summable lam mu hlam hmu i n 0)
    (by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith)

lemma Vser_hasDerivAt (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) (t : ℝ) :
    HasDerivAt (Vser lam mu i n)
      (∑' k : ℕ, t ^ k / (k.factorial : ℝ) * kerA lam mu i (k + 1) n) t := by
  have key := Vser_hasDerivAt0 lam mu hlam hmu i n t
  have hfun : (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * t ^ (k + 1 - 1) / ((k + 1).factorial : ℝ)
      * kerA lam mu i (k + 1) n) = fun k : ℕ => t ^ k / (k.factorial : ℝ) * kerA lam mu i (k + 1) n := by
    funext k
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hsum : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * t ^ (k + 1 - 1) / ((k + 1).factorial : ℝ)
      * kerA lam mu i (k + 1) n) := by
    rw [hfun]; exact Vser_shift_summable lam mu hlam hmu i n t
  rw [tsum_eq_zero_add'
    (f := fun k : ℕ => (k : ℝ) * t ^ (k - 1) / (k.factorial : ℝ) * kerA lam mu i k n) hsum,
    hfun] at key
  have h0 : ((0 : ℕ) : ℝ) * t ^ (0 - 1) / ((0 : ℕ).factorial : ℝ) * kerA lam mu i 0 n = 0 := by simp
  rw [h0, zero_add] at key
  unfold Vser
  exact key

lemma shift_eq (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) (t : ℝ) :
    ∑' k : ℕ, t ^ k / (k.factorial : ℝ) * kerA lam mu i (k + 1) n
      = stepS lam mu (fun m => Vser lam mu i m t) n := by
  have hs := fun m => Vser_summable lam mu hlam hmu i m t
  cases n with
  | zero =>
    have e : (fun k : ℕ => t ^ k / (k.factorial : ℝ) * kerA lam mu i (k + 1) 0) = fun k : ℕ =>
        mu * (t ^ k / (k.factorial : ℝ) * kerA lam mu i k 0)
          + mu * (t ^ k / (k.factorial : ℝ) * kerA lam mu i k 1) := by
      funext k; simp only [kerA, stepS]; ring
    rw [e, ((hs 0).mul_left mu).tsum_add ((hs 1).mul_left mu), tsum_mul_left, tsum_mul_left]
    rfl
  | succ n =>
    have e : (fun k : ℕ => t ^ k / (k.factorial : ℝ) * kerA lam mu i (k + 1) (n + 1)) = fun k : ℕ =>
        lam * (t ^ k / (k.factorial : ℝ) * kerA lam mu i k n)
          + mu * (t ^ k / (k.factorial : ℝ) * kerA lam mu i k (n + 2)) := by
      funext k; simp only [kerA, stepS]; ring
    rw [e, ((hs n).mul_left lam).tsum_add ((hs (n + 2)).mul_left mu), tsum_mul_left, tsum_mul_left]
    rfl

/-- T6: a probability solution of (2.72) exists (uniformization). -/
theorem mm1_exists_probability_solution (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ) :
    ∃ u : ℕ → ℝ → ℝ, IsForwardSolution (mm1RHS lam mu) u ∧ IsProbabilityFamily u ∧
      ∀ n : ℕ, u n 0 = if n = i then 1 else 0 := by
  refine ⟨fun n t => Real.exp (-(lam + mu) * t) * Vser lam mu i n t, ?_, ?_, ?_⟩
  · intro n t _
    have h1 : HasDerivAt (fun t : ℝ => -(lam + mu) * t) (-(lam + mu)) t := by
      simpa using (hasDerivAt_id t).const_mul (-(lam + mu))
    have := (h1.exp.mul (Vser_hasDerivAt lam mu hlam hmu i n t)).hasDerivWithinAt
      (s := Set.Ici (0 : ℝ))
    refine this.congr_deriv ?_
    rw [shift_eq lam mu hlam hmu i n t]
    cases n <;> simp only [mm1RHS, stepS] <;> ring
  · intro t ht
    refine ⟨fun n => mul_nonneg (Real.exp_pos _).le
      (tsum_nonneg fun k => mul_nonneg (by positivity) (kerA_nonneg lam mu hlam hmu i k n)), ?_⟩
    set F : ℕ × ℕ → ℝ := fun p => t ^ p.1 / (p.1.factorial : ℝ) * kerA lam mu i p.1 p.2 with hF
    have hF0 : 0 ≤ F := fun p => mul_nonneg (by positivity) (kerA_nonneg lam mu hlam hmu i _ _)
    have hrow : ∀ k : ℕ, HasSum (fun n => F (k, n)) (t ^ k / (k.factorial : ℝ) * (lam + mu) ^ k) :=
      fun k => (kerA_hasSum lam mu i k).mul_left _
    have hcol : HasSum (fun k : ℕ => t ^ k / (k.factorial : ℝ) * (lam + mu) ^ k)
        (Real.exp ((lam + mu) * t)) := by
      have h := NormedSpace.expSeries_div_hasSum_exp ((lam + mu) * t)
      rw [← Real.exp_eq_exp_ℝ] at h
      have e : (fun k : ℕ => t ^ k / (k.factorial : ℝ) * (lam + mu) ^ k) =
          fun k : ℕ => ((lam + mu) * t) ^ k / (k.factorial : ℝ) := by
        funext k; rw [mul_pow]; ring
      rw [e]; exact h
    have hrowfun : (fun k : ℕ => ∑' n, F (k, n)) =
        fun k : ℕ => t ^ k / (k.factorial : ℝ) * (lam + mu) ^ k :=
      funext fun k => (hrow k).tsum_eq
    have hFs : Summable F :=
      (summable_prod_of_nonneg hF0).2 ⟨fun k => (hrow k).summable, by rw [hrowfun]; exact hcol.summable⟩
    have htot : HasSum F (Real.exp ((lam + mu) * t)) := by
      have := hFs.hasSum.prod_fiberwise (fun k => hrow k)
      rw [hcol.unique this]
      exact hFs.hasSum
    have hswap : HasSum (fun p : ℕ × ℕ => F (p.2, p.1)) (Real.exp ((lam + mu) * t)) :=
      (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr htot
    have hV : HasSum (fun n => Vser lam mu i n t) (Real.exp ((lam + mu) * t)) :=
      hswap.prod_fiberwise (fun n => (Vser_summable lam mu hlam hmu i n t).hasSum)
    have := hV.mul_left (Real.exp (-(lam + mu) * t))
    rw [← Real.exp_add, show -(lam + mu) * t + (lam + mu) * t = 0 by ring, Real.exp_zero] at this
    exact this
  · intro n
    show Real.exp (-(lam + mu) * 0) * Vser lam mu i n 0 = _
    rw [Vser, tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
    simp [kerA]

end MM1Aux12395959

namespace MM1Aux12395959
open QueueingFundamentals.Transient

lemma prob_bdd {q : ℕ → ℝ → ℝ} (hq : IsProbabilityFamily q) :
    ∀ T : ℝ, ∃ C : ℝ, ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T, |q n t| ≤ C := by
  intro T
  refine ⟨1, fun n t ht => ?_⟩
  obtain ⟨hnn, hs⟩ := hq t ht.1
  rw [abs_of_nonneg (hnn n)]
  exact le_hasSum hs n (fun m _ => hnn m)

end MM1Aux12395959

open QueueingFundamentals.Transient in
theorem solution (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ) :
    (∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
        Summable (fun j : ℕ => (lam / mu) ^ (-(((j + n + i + 2 : ℕ) : ℝ)) / 2)
          * besselI (j + n + i + 2) (2 * t * Real.sqrt (lam * mu)))) ∧
      IsForwardSolution (mm1RHS lam mu) (fun n t => mm1Transient lam mu i n t) ∧
      (∀ n : ℕ, mm1Transient lam mu i n 0 = if n = i then 1 else 0) ∧
      IsProbabilityFamily (fun n t => mm1Transient lam mu i n t) ∧
      ∀ q : ℕ → ℝ → ℝ, IsForwardSolution (mm1RHS lam mu) q → IsProbabilityFamily q →
        (∀ n : ℕ, q n 0 = if n = i then 1 else 0) →
        ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → q n t = mm1Transient lam mu i n t := by
  have hF := MM1Aux12395959.mm1Transient_isForwardSolution lam mu hlam hmu i
  obtain ⟨hinit, hbdd⟩ := MM1Aux12395959.mm1Transient_init_bdd lam mu hlam hmu i
  obtain ⟨u, hu, hup, hu0⟩ := MM1Aux12395959.mm1_exists_probability_solution lam mu hlam hmu i
  have heq : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → u n t = mm1Transient lam mu i n t :=
    MM1Aux12395959.mm1_forward_unique lam mu hlam hmu u _ hu hF (fun n => by rw [hu0, hinit]) (MM1Aux12395959.prob_bdd hup) hbdd
  refine ⟨MM1Aux12395959.mm1_tail_summable lam mu hlam hmu i, hF, hinit, fun t ht => ?_, fun q hq hqp hq0 => ?_⟩
  · obtain ⟨hnn, hs⟩ := hup t ht
    refine ⟨fun n => by show 0 ≤ mm1Transient lam mu i n t; rw [← heq n t ht]; exact hnn n, ?_⟩
    have : (fun n => mm1Transient lam mu i n t) = fun n => u n t := funext fun n => (heq n t ht).symm
    rw [this]; exact hs
  · exact MM1Aux12395959.mm1_forward_unique lam mu hlam hmu q _ hq hF (fun n => by rw [hq0, hinit])
      (MM1Aux12395959.prob_bdd hqp) hbdd
