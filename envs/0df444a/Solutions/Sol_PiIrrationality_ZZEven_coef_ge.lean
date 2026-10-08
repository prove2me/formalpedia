-- Prove2me | solution 1 for PiIrrationality.ZZEven.coef_ge
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T09:47:27.726035+00:00
-- url     : https://prove2.me/submissions/c4b2c889-3ec4-4d0c-9183-b521b38c7d74

import Definitions.Def_PiIrrationality_ZZEvenForms
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open Polynomial Filter

namespace PiIrrationality.ZZEven.CoefGe


/-- The binomial term `T(i) = C(N,i) M^i (N-M)^(N-i)`. -/
def T (N M i : ℕ) : ℕ := N.choose i * M ^ i * (N - M) ^ (N - i)

lemma T_step (N M i : ℕ) (hi : i < N) :
    T N M (i + 1) * ((i + 1) * (N - M)) = T N M i * ((N - i) * M) := by
  unfold T
  have h1 := Nat.choose_succ_right_eq N i
  obtain ⟨k, hk⟩ : ∃ k, N - i = k + 1 := ⟨N - i - 1, by omega⟩
  have hk' : N - (i + 1) = k := by omega
  rw [hk] at h1
  rw [hk, hk']
  calc N.choose (i + 1) * M ^ (i + 1) * (N - M) ^ k * ((i + 1) * (N - M))
      = (N.choose (i + 1) * (i + 1)) * M ^ i * M * (N - M) ^ k * (N - M) := by ring
    _ = (N.choose i * (k + 1)) * M ^ i * M * (N - M) ^ k * (N - M) := by rw [h1]
    _ = N.choose i * M ^ i * (N - M) ^ (k + 1) * ((k + 1) * M) := by ring

lemma T_mono_up (N M : ℕ) (hMN : M ≤ N) : ∀ i, i < M → T N M i ≤ T N M (i + 1) := by
  intro i hi
  rcases Nat.eq_or_lt_of_le hMN with h | h
  · -- N = M: T i = 0 for i < N
    unfold T
    have h0 : N - M = 0 := by omega
    rw [h0, zero_pow (show N - i ≠ 0 by omega)]
    simp
  · have hpos : 0 < (i + 1) * (N - M) := Nat.mul_pos (by omega) (by omega)
    have hstep := T_step N M i (by omega)
    have hineq : (i + 1) * (N - M) ≤ (N - i) * M := by
      have e : (N - i) * M = (i + 1) * (N - M) + (N * (M - (i + 1)) + M) := by
        zify [show i ≤ N by omega, hMN, show i + 1 ≤ M by omega]
        ring
      omega
    by_contra hcon
    push Not at hcon
    have : T N M (i + 1) * ((i + 1) * (N - M)) < T N M i * ((i + 1) * (N - M)) :=
      Nat.mul_lt_mul_of_pos_right hcon hpos
    have : T N M i * ((i + 1) * (N - M)) ≤ T N M i * ((N - i) * M) :=
      Nat.mul_le_mul_left _ hineq
    omega

lemma T_mono_down (N M : ℕ) (hMN : M ≤ N) :
    ∀ i, M ≤ i → i < N → T N M (i + 1) ≤ T N M i := by
  intro i hi hiN
  have hpos : 0 < (i + 1) * (N - M) := Nat.mul_pos (by omega) (by omega)
  have hstep := T_step N M i hiN
  have hineq : (N - i) * M ≤ (i + 1) * (N - M) := by
    have e : (i + 1) * (N - M) = (N - i) * M + (N * (i + 1 - M) - M) := by
      have h3 : M ≤ N * (i + 1 - M) := by
        calc M ≤ N := hMN
          _ = N * 1 := (mul_one N).symm
          _ ≤ N * (i + 1 - M) := Nat.mul_le_mul_left _ (by omega)
      zify [show i ≤ N by omega, hMN, show M ≤ i + 1 by omega, h3]
      ring
    omega
  by_contra hcon
  push Not at hcon
  have : T N M i * ((i + 1) * (N - M)) < T N M (i + 1) * ((i + 1) * (N - M)) :=
    Nat.mul_lt_mul_of_pos_right hcon hpos
  have : T N M i * ((N - i) * M) ≤ T N M i * ((i + 1) * (N - M)) := Nat.mul_le_mul_left _ hineq
  omega

lemma T_up (N M : ℕ) (hMN : M ≤ N) (i : ℕ) :
    ∀ d, i + d ≤ M → T N M i ≤ T N M (i + d) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h
    calc T N M i ≤ T N M (i + d) := ih (by omega)
      _ ≤ T N M (i + d + 1) := T_mono_up N M hMN (i + d) (by omega)
      _ = T N M (i + (d + 1)) := by ring_nf

lemma T_down (N M : ℕ) (hMN : M ≤ N) :
    ∀ d, M + d ≤ N → T N M (M + d) ≤ T N M M := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h
    calc T N M (M + (d + 1)) = T N M (M + d + 1) := by ring_nf
      _ ≤ T N M (M + d) := T_mono_down N M hMN (M + d) (by omega) (by omega)
      _ ≤ T N M M := ih (by omega)

lemma T_le_mode (N M : ℕ) (hMN : M ≤ N) : ∀ i, i ≤ N → T N M i ≤ T N M M := by
  intro i hiN
  rcases le_or_gt i M with h | h
  · have := T_up N M hMN i (M - i) (by omega)
    rwa [Nat.add_sub_cancel' h] at this
  · have := T_down N M hMN (i - M) (by omega)
    rwa [Nat.add_sub_cancel' h.le] at this

/-- The entropy lower bound for binomial coefficients, in `ℕ`. -/
theorem pow_le_choose_mul (N M : ℕ) (hMN : M ≤ N) :
    N ^ N ≤ (N + 1) * (N.choose M * M ^ M * (N - M) ^ (N - M)) := by
  have hsum : N ^ N = ∑ i ∈ Finset.range (N + 1), T N M i := by
    have := add_pow (M : ℕ) (N - M) N
    rw [Nat.add_sub_cancel' hMN] at this
    rw [this]
    apply Finset.sum_congr rfl
    intro i _
    simp only [T, Nat.cast_id]; ring
  rw [hsum]
  calc ∑ i ∈ Finset.range (N + 1), T N M i ≤ ∑ _i ∈ Finset.range (N + 1), T N M M :=
        Finset.sum_le_sum fun i hi => T_le_mode N M hMN i (by simpa [Nat.lt_succ_iff] using hi)
    _ = (N + 1) * T N M M := by simp
    _ = (N + 1) * (N.choose M * M ^ M * (N - M) ^ (N - M)) := rfl


/-! ### Coefficient lower bounds in `ℕ[X]` -/

/-- A coefficient of a product is at least the product of two coefficients. -/
lemma coeff_mul_ge (f g : ℕ[X]) (a b : ℕ) : f.coeff a * g.coeff b ≤ (f * g).coeff (a + b) := by
  rw [coeff_mul]
  exact Finset.single_le_sum (f := fun x : ℕ × ℕ => f.coeff x.1 * g.coeff x.2)
    (fun _ _ => Nat.zero_le _)
    (show (a, b) ∈ Finset.antidiagonal (a + b) from Finset.mem_antidiagonal.mpr rfl)

/-- One term of the binomial expansion bounds the coefficient of a power of a sum. -/
lemma coeff_add_pow_ge (p r : ℕ[X]) (m j k : ℕ) :
    (p ^ j * r ^ (m - j)).coeff k * m.choose j ≤ ((p + r) ^ m).coeff k := by
  rcases le_or_gt j m with hj | hj
  · rw [add_pow, finsetSum_coeff]
    have := Finset.single_le_sum (f := fun i => (p ^ i * r ^ (m - i) * (m.choose i : ℕ[X])).coeff k)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    simpa [coeff_mul_natCast] using this
  · simp [Nat.choose_eq_zero_of_lt hj]

lemma two_eq : (C 2 : ℕ[X]) = 2 := by simp [map_ofNat]

lemma A_eq : A =
    (1 + X) ^ 4 * ((X * (X + C 2) + C 2) ^ 4 * ((C 2 * X) * (X + 1) + 1) ^ 4) := by
  unfold A
  simp only [map_ofNat]
  ring

lemma A_pow (n : ℕ) : A ^ n =
    (1 + X) ^ (4 * n) * ((X * (X + C 2) + C 2) ^ (4 * n) * ((C 2 * X) * (X + 1) + 1) ^ (4 * n)) := by
  rw [A_eq, mul_pow, mul_pow, pow_mul, pow_mul, pow_mul]

/-- The `(X^2+2X+2)^m` coefficient at `j + l`. -/
lemma coeff_P1 (m j l : ℕ) :
    m.choose j * 2 ^ (m - j) * (2 ^ (j - l) * j.choose l) ≤
      ((X * (X + C 2) + C 2 : ℕ[X]) ^ m).coeff (j + l) := by
  refine le_trans ?_ (coeff_add_pow_ge _ _ m j (j + l))
  rw [mul_pow, ← C_pow, mul_assoc, coeff_mul_C, add_comm j l, coeff_X_pow_mul,
    coeff_X_add_C_pow]
  apply le_of_eq; simp only [Nat.cast_id]; ring

/-- The `(2X^2+2X+1)^m` coefficient at `j + l`. -/
lemma coeff_P2 (m j l : ℕ) :
    m.choose j * (2 ^ j * j.choose l) ≤ (((C 2 * X) * (X + 1) + 1 : ℕ[X]) ^ m).coeff (j + l) := by
  refine le_trans ?_ (coeff_add_pow_ge _ _ m j (j + l))
  rw [one_pow, mul_one, mul_pow, mul_pow, ← C_pow, mul_assoc, coeff_C_mul, add_comm j l,
    coeff_X_pow_mul, coeff_X_add_one_pow]
  apply le_of_eq; simp only [Nat.cast_id]; ring

/-- `C(N+a, M+b) ≥ C(N, M)` whenever `b ≤ a`. -/
lemma choose_le_choose_add (N M a b : ℕ) (hab : b ≤ a) :
    N.choose M ≤ (N + a).choose (M + b) := by
  have h1 : ∀ b, N.choose M ≤ (N + b).choose (M + b) := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      calc N.choose M ≤ (N + b).choose (M + b) := ih
        _ ≤ (N + b).choose (M + b) + (N + b).choose (M + b + 1) := Nat.le_add_right _ _
        _ = (N + (b + 1)).choose (M + (b + 1)) := by
          rw [show N + (b + 1) = (N + b) + 1 by ring, show M + (b + 1) = (M + b) + 1 by ring,
            Nat.choose_succ_succ]
  calc N.choose M ≤ (N + b).choose (M + b) := h1 b
    _ ≤ (N + a).choose (M + b) := Nat.choose_le_choose _ (by omega)

/-- The single-term lower bound for `coef n` with `q = n / 10`. -/
theorem coef_ge_term (n : ℕ) (hq1 : 1 ≤ n / 10) :
    let q := n / 10
    (40 * q).choose (8 * q) *
      (((40 * q).choose (8 * q) * 2 ^ (32 * q) * (2 ^ (7 * q) * (8 * q).choose q)) *
        ((40 * q).choose (15 * q) * (2 ^ (15 * q) * (15 * q).choose (3 * q)))) *
      (105 * q - 1).choose (25 * q) ≤ coef n := by
  intro q
  have hq : 1 ≤ q := hq1
  have hn : n = 10 * q + n % 10 := (Nat.div_add_mod n 10).symm
  set r := n % 10
  -- the single term k = 35 q of the defining sum
  have hk : 35 * q ∈ Finset.range (6 * n + 1) := by
    rw [Finset.mem_range]; omega
  have hterm := Finset.single_le_sum (f := fun k =>
      (A ^ n).coeff k * Nat.choose (8 * n - 1 + (6 * n - k)) (6 * n - k))
      (fun _ _ => Nat.zero_le _) hk
  refine le_trans ?_ hterm
  apply Nat.mul_le_mul
  · -- coefficient of A^n at 35 q
    have hsplit : A ^ n = A ^ (10 * q) * A ^ r := by rw [← pow_add, ← hn]
    have hA0 : 1 ≤ (A ^ r).coeff 0 := by
      rw [coeff_zero_eq_eval_zero, eval_pow]
      apply Nat.one_le_pow
      unfold A; simp [map_ofNat]
    calc _ ≤ (A ^ (10 * q)).coeff (35 * q) := ?_
      _ ≤ (A ^ (10 * q)).coeff (35 * q) * (A ^ r).coeff 0 := Nat.le_mul_of_pos_right _ hA0
      _ ≤ (A ^ n).coeff (35 * q) := by rw [hsplit]; exact coeff_mul_ge _ _ _ 0
    rw [A_pow, show 4 * (10 * q) = 40 * q by ring]
    have e : 35 * q = 8 * q + ((8 * q + q) + (15 * q + 3 * q)) := by ring
    rw [e]
    refine le_trans ?_ (coeff_mul_ge _ _ _ _)
    apply Nat.mul_le_mul (by rw [coeff_one_add_X_pow, Nat.cast_id])
    refine le_trans ?_ (coeff_mul_ge _ _ _ _)
    apply Nat.mul_le_mul
    · have := coeff_P1 (40 * q) (8 * q) q
      rw [show 40 * q - 8 * q = 32 * q by omega, show 8 * q - q = 7 * q by omega] at this
      exact this
    · exact coeff_P2 (40 * q) (15 * q) (3 * q)
  · -- the negative binomial factor
    have e1 : 8 * n - 1 + (6 * n - 35 * q) = (105 * q - 1) + 14 * r := by omega
    have e2 : 6 * n - 35 * q = 25 * q + 6 * r := by omega
    rw [e1, e2]
    exact choose_le_choose_add _ _ _ _ (by omega)


/-! ### From the single term to an exponential lower bound -/

/-- `E α β = α^α / (β^β (α-β)^(α-β))`. -/
noncomputable def E (α β : ℕ) : ℝ := (α : ℝ) ^ α / ((β : ℝ) ^ β * ((α - β : ℕ) : ℝ) ^ (α - β))

lemma E_pos (α β : ℕ) (h : β < α) (hβ : 0 < β) : 0 < E α β := by
  unfold E
  have : (0 : ℝ) < ((α - β : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt h
  have : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have : (0 : ℝ) < (α : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le β) h)
  positivity

/-- Scaled entropy bound: `E(α,β)^q ≤ (αq+1) C(αq, βq)`. -/
lemma choose_ge_real (α β q : ℕ) (h : β < α) (hβ : 0 < β) (hq : 0 < q) :
    E α β ^ q ≤ ((α * q + 1 : ℕ) : ℝ) * ((α * q).choose (β * q) : ℝ) := by
  have hnat := pow_le_choose_mul (α * q) (β * q) (Nat.mul_le_mul_right q h.le)
  have hsub : α * q - β * q = (α - β) * q := (Nat.sub_mul α β q).symm
  rw [hsub] at hnat
  have hR : ((α * q : ℕ) : ℝ) ^ (α * q) ≤ ((α * q + 1 : ℕ) : ℝ) *
      (((α * q).choose (β * q) : ℝ) * ((β * q : ℕ) : ℝ) ^ (β * q) *
        (((α - β) * q : ℕ) : ℝ) ^ ((α - β) * q)) := by exact_mod_cast hnat
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast hβ
  have hαβ : (0 : ℝ) < ((α - β : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt h
  have hqpow : (0 : ℝ) < (q : ℝ) ^ (α * q) := pow_pos hq0 _
  -- rewrite both sides with q^(αq) factored out
  have hl : ((α * q : ℕ) : ℝ) ^ (α * q) = ((α : ℝ) ^ α) ^ q * (q : ℝ) ^ (α * q) := by
    push_cast; rw [mul_pow, ← pow_mul]
  have hαeq : α * q = β * q + (α - β) * q := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' h.le]
  have hr : ((β * q : ℕ) : ℝ) ^ (β * q) * (((α - β) * q : ℕ) : ℝ) ^ ((α - β) * q) =
      ((β : ℝ) ^ β * ((α - β : ℕ) : ℝ) ^ (α - β)) ^ q * (q : ℝ) ^ (α * q) := by
    rw [hαeq, pow_add]
    push_cast
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    ring
  rw [hl, mul_assoc ((α * q).choose (β * q) : ℝ), hr] at hR
  have hden : 0 < (β : ℝ) ^ β * ((α - β : ℕ) : ℝ) ^ (α - β) := by positivity
  unfold E
  rw [div_pow, div_le_iff₀ (pow_pos hden q)]
  have := le_of_mul_le_mul_right (a := (q : ℝ) ^ (α * q))
    (by calc ((α : ℝ) ^ α) ^ q * (q : ℝ) ^ (α * q) ≤ _ := hR
      _ = ((α * q + 1 : ℕ) : ℝ) * ((α * q).choose (β * q) : ℝ) *
          ((β : ℝ) ^ β * ((α - β : ℕ) : ℝ) ^ (α - β)) ^ q * (q : ℝ) ^ (α * q) := by ring) hqpow
  linarith

/-- The constant `R` of the single-term bound. -/
noncomputable def Rc : ℝ := E 40 8 * E 40 8 * E 8 1 * E 40 15 * E 15 3 * E 105 25 * 2 ^ 54

lemma Rc_gt : (107 / 100 : ℝ) * (271829 / 100000) ^ 172 ≤ Rc := by
  unfold Rc E
  norm_num

lemma exp_172_le : Real.exp 172 ≤ (271829 / 100000 : ℝ) ^ 172 := by
  have h := Real.exp_one_lt_d9
  rw [show (172 : ℝ) = (172 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le (by norm_num at h ⊢; linarith) 172


/-- The single term, in real form: `Rc^q ≤ D(q) · coef n`. -/
lemma Rc_pow_le (n : ℕ) (hq1 : 1 ≤ n / 10) :
    Rc ^ (n / 10) ≤ ((40 * (n / 10) + 1 : ℕ) : ℝ) ^ 3 * ((8 * (n / 10) + 1 : ℕ) : ℝ) *
      ((15 * (n / 10) + 1 : ℕ) : ℝ) * ((105 * (n / 10) + 1 : ℕ) : ℝ) * (105 / 80) *
      (coef n : ℝ) := by
  set q := n / 10 with hqdef
  have hq : 0 < q := hq1
  have hterm := coef_ge_term n hq1
  simp only at hterm
  rw [← hqdef] at hterm
  have hterm' : ((40 * q).choose (8 * q) : ℝ) * ((40 * q).choose (8 * q) : ℝ) *
      ((8 * q).choose q : ℝ) * ((40 * q).choose (15 * q) : ℝ) * ((15 * q).choose (3 * q) : ℝ) *
      ((105 * q - 1).choose (25 * q) : ℝ) * (2 : ℝ) ^ (54 * q) ≤ (coef n : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hterm
    push_cast at this
    calc _ = ((40 * q).choose (8 * q) : ℝ) *
          (((40 * q).choose (8 * q) : ℝ) * 2 ^ (32 * q) * (2 ^ (7 * q) * ((8 * q).choose q : ℝ)) *
            (((40 * q).choose (15 * q) : ℝ) * (2 ^ (15 * q) * ((15 * q).choose (3 * q) : ℝ)))) *
          ((105 * q - 1).choose (25 * q) : ℝ) := by
            rw [show 54 * q = 32 * q + 7 * q + 15 * q by ring, pow_add, pow_add]; ring
      _ ≤ (coef n : ℝ) := this
  -- the shifted binomial
  have h105 : ((105 * q).choose (25 * q) : ℝ) * 80 ≤ ((105 * q - 1).choose (25 * q) : ℝ) * 105 := by
    have hc := Nat.choose_mul_succ_eq (105 * q - 1) (25 * q)
    rw [show 105 * q - 1 + 1 = 105 * q by omega, show 105 * q - 25 * q = 80 * q by omega] at hc
    have hc' : ((105 * q - 1).choose (25 * q) : ℝ) * (105 * q) = ((105 * q).choose (25 * q) : ℝ) * (80 * q) := by
      exact_mod_cast hc
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    nlinarith
  have e1 := choose_ge_real 40 8 q (by norm_num) (by norm_num) hq
  have e2 := choose_ge_real 8 1 q (by norm_num) (by norm_num) hq
  have e3 := choose_ge_real 40 15 q (by norm_num) (by norm_num) hq
  have e4 := choose_ge_real 15 3 q (by norm_num) (by norm_num) hq
  have e5 := choose_ge_real 105 25 q (by norm_num) (by norm_num) hq
  rw [one_mul] at e2
  have p1 := E_pos 40 8 (by norm_num) (by norm_num)
  have p2 := E_pos 8 1 (by norm_num) (by norm_num)
  have p3 := E_pos 40 15 (by norm_num) (by norm_num)
  have p4 := E_pos 15 3 (by norm_num) (by norm_num)
  have p5 := E_pos 105 25 (by norm_num) (by norm_num)
  have hRc : Rc ^ q = E 40 8 ^ q * E 40 8 ^ q * E 8 1 ^ q * E 40 15 ^ q * E 15 3 ^ q *
      E 105 25 ^ q * (2 : ℝ) ^ (54 * q) := by
    unfold Rc; rw [pow_mul]; simp only [mul_pow]
  rw [hRc]
  -- multiply the six entropy bounds
  have hprod := mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul e1 e1 (by positivity)
    (by positivity)) e2 (by positivity) (by positivity)) e3 (by positivity) (by positivity)) e4
    (by positivity) (by positivity)) e5 (by positivity) (by positivity)
  have h2 : (0 : ℝ) < 2 ^ (54 * q) := by positivity
  have hfinal := mul_le_mul_of_nonneg_right hprod h2.le
  refine le_trans hfinal ?_
  have hnn : ∀ m : ℕ, (0 : ℝ) ≤ (m : ℝ) := fun m => Nat.cast_nonneg m
  have hB := hterm'
  -- compare coefficientwise
  calc _ = ((40 * q + 1 : ℕ) : ℝ) ^ 3 * ((8 * q + 1 : ℕ) : ℝ) * ((15 * q + 1 : ℕ) : ℝ) *
        ((105 * q + 1 : ℕ) : ℝ) *
        (((40 * q).choose (8 * q) : ℝ) * ((40 * q).choose (8 * q) : ℝ) *
          ((8 * q).choose q : ℝ) * ((40 * q).choose (15 * q) : ℝ) * ((15 * q).choose (3 * q) : ℝ) *
          ((105 * q).choose (25 * q) : ℝ) * (2 : ℝ) ^ (54 * q)) := by ring
    _ ≤ ((40 * q + 1 : ℕ) : ℝ) ^ 3 * ((8 * q + 1 : ℕ) : ℝ) * ((15 * q + 1 : ℕ) : ℝ) *
        ((105 * q + 1 : ℕ) : ℝ) * (105 / 80) *
        (((40 * q).choose (8 * q) : ℝ) * ((40 * q).choose (8 * q) : ℝ) *
          ((8 * q).choose q : ℝ) * ((40 * q).choose (15 * q) : ℝ) * ((15 * q).choose (3 * q) : ℝ) *
          ((105 * q - 1).choose (25 * q) : ℝ) * (2 : ℝ) ^ (54 * q)) := by
        have hX : (0 : ℝ) ≤ ((40 * q + 1 : ℕ) : ℝ) ^ 3 * ((8 * q + 1 : ℕ) : ℝ) *
            ((15 * q + 1 : ℕ) : ℝ) * ((105 * q + 1 : ℕ) : ℝ) := by positivity
        have hY : (0 : ℝ) ≤ ((40 * q).choose (8 * q) : ℝ) * ((40 * q).choose (8 * q) : ℝ) *
            ((8 * q).choose q : ℝ) * ((40 * q).choose (15 * q) : ℝ) *
            ((15 * q).choose (3 * q) : ℝ) * (2 : ℝ) ^ (54 * q) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h105 (mul_nonneg hX hY)]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hB; positivity

end PiIrrationality.ZZEven.CoefGe

open PiIrrationality.ZZEven PiIrrationality.ZZEven.CoefGe in
theorem solution :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.exp (1720 / 100 * (n : ℝ)) ≤ (PiIrrationality.ZZEven.coef n : ℝ) := by
  -- polynomial factor is eventually dominated by 1.07^q
  set c : ℝ := 41 ^ 3 * 9 * 16 * 106 * (105 / 80) * (271829 / 100000 : ℝ) ^ 172 with hc
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 6 (show (1 : ℝ) < 107 / 100 by norm_num)
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / c by positivity))
  obtain ⟨Q0, hQ0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨10 * (Q0 + 1), fun n hn => ?_⟩
  set q := n / 10 with hqdef
  have hqQ : Q0 + 1 ≤ q := by omega
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hcoef := Rc_pow_le n hq1
  rw [← hqdef] at hcoef
  have hpoly := hQ0 q (by omega)
  have hcpos : 0 < c := by positivity
  -- q^6 < 1.07^q / c
  have h107 : (0 : ℝ) < (107 / 100) ^ q := by positivity
  have hpoly' : c * (q : ℝ) ^ 6 < (107 / 100) ^ q := by
    rw [div_lt_div_iff₀ h107 hcpos] at hpoly
    linarith
  -- the polynomial prefactor is at most (c / (2.71829^172)) q^6
  have hD : ((40 * q + 1 : ℕ) : ℝ) ^ 3 * ((8 * q + 1 : ℕ) : ℝ) * ((15 * q + 1 : ℕ) : ℝ) *
      ((105 * q + 1 : ℕ) : ℝ) * (105 / 80) ≤ 41 ^ 3 * 9 * 16 * 106 * (105 / 80) * (q : ℝ) ^ 6 := by
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    push_cast
    have a1 : (40 * (q : ℝ) + 1) ≤ 41 * q := by linarith
    have a2 : (8 * (q : ℝ) + 1) ≤ 9 * q := by linarith
    have a3 : (15 * (q : ℝ) + 1) ≤ 16 * q := by linarith
    have a4 : (105 * (q : ℝ) + 1) ≤ 106 * q := by linarith
    calc (40 * (q : ℝ) + 1) ^ 3 * (8 * q + 1) * (15 * q + 1) * (105 * q + 1) * (105 / 80)
        ≤ (41 * q) ^ 3 * (9 * q) * (16 * q) * (106 * q) * (105 / 80) := by gcongr
      _ = 41 ^ 3 * 9 * 16 * 106 * (105 / 80) * (q : ℝ) ^ 6 := by ring
  have hRc := Rc_gt
  have he := exp_172_le
  -- exp(17.2 n) ≤ exp 172 ^ (q + 1)
  have hn10 : (n : ℝ) ≤ 10 * q + 10 := by
    have : n < 10 * q + 10 := by omega
    exact_mod_cast this.le
  have hexp : Real.exp (1720 / 100 * n) ≤ Real.exp 172 ^ (q + 1) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  -- Rc^q ≥ 1.07^q * 2.71829^(172 q)
  have hRq : (107 / 100 : ℝ) ^ q * ((271829 / 100000 : ℝ) ^ 172) ^ q ≤ Rc ^ q := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hRc q
  have hE : Real.exp 172 ^ (q + 1) ≤ ((271829 / 100000 : ℝ) ^ 172) ^ (q + 1) :=
    pow_le_pow_left₀ (Real.exp_pos _).le he _
  set T : ℝ := (271829 / 100000 : ℝ) ^ 172 with hT
  have hTpos : 0 < T := by positivity
  have hcoef' : Rc ^ q ≤ 41 ^ 3 * 9 * 16 * 106 * (105 / 80) * (q : ℝ) ^ 6 * (coef n : ℝ) := by
    refine le_trans hcoef ?_
    exact mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg _)
  -- combine
  have hc' : c = 41 ^ 3 * 9 * 16 * 106 * (105 / 80) * T := by rw [hc, hT]
  have hcoefpos : (0 : ℝ) ≤ coef n := Nat.cast_nonneg _
  have hq6 : (0 : ℝ) < (q : ℝ) ^ 6 := by positivity
  have hTq : (0 : ℝ) < T ^ q := by positivity
  calc Real.exp (1720 / 100 * n) ≤ T ^ (q + 1) := hexp.trans hE
    _ = T * T ^ q := by rw [pow_succ]; ring
    _ ≤ (coef n : ℝ) := by
        -- T^(q+1) * c' q^6 < 1.07^q T^q ≤ Rc^q ≤ c' q^6 coef
        have k1 : T * T ^ q * (41 ^ 3 * 9 * 16 * 106 * (105 / 80) * (q : ℝ) ^ 6) ≤
            (107 / 100 : ℝ) ^ q * T ^ q := by
          have := mul_lt_mul_of_pos_right hpoly' hTq
          rw [hc'] at this
          nlinarith
        have k2 := hRq.trans hcoef'
        have hK : (0 : ℝ) < 41 ^ 3 * 9 * 16 * 106 * (105 / 80) * (q : ℝ) ^ 6 := by positivity
        have := k1.trans k2
        rw [mul_comm (41 ^ 3 * 9 * 16 * 106 * (105 / 80) * (q : ℝ) ^ 6) (coef n : ℝ)] at this
        exact le_of_mul_le_mul_right this hK
