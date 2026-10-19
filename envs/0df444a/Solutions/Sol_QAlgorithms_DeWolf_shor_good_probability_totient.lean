-- Prove2me | solution 1 for QAlgorithms.DeWolf.shor_good_probability_totient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:44:04.021922+00:00
-- url     : https://prove2.me/submissions/06ca6fff-6cf9-40d4-bd09-6f22b96649ef

import Definitions.Def_QAlgorithms_Defs_Fourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxHeartbeats 800000
open QAlgorithms
open scoped Real ComplexConjugate

private noncomputable def wave (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * (t : ℂ))

private lemma wave_add (x y : ℝ) : wave (x + y) = wave x * wave y := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma wave_int (k : ℤ) : wave k = 1 := by
  unfold wave
  push_cast
  convert Complex.exp_int_mul_two_pi_mul_I k using 1 <;> ring

private lemma wave_norm (x : ℝ) : ‖wave x‖ = 1 := by
  unfold wave
  rw [show 2 * (π : ℂ) * Complex.I * (x : ℂ) = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma wave_norm_sub (t : ℝ) :
    Complex.normSq (wave t - 1) = 4 * Real.sin (π * t) ^ 2 := by
  unfold wave
  rw [show 2 * (π : ℂ) * Complex.I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hc := Real.cos_two_mul (π * t)
  have ht := Real.sin_sq_add_cos_sq (2 * π * t)
  rw [show 2 * π * t = 2 * (π * t) by ring] at ht ⊢
  nlinarith [Real.sin_sq_add_cos_sq (π * t)]

private lemma wave_sum_lower (q : ℕ) (hq : 0 < q) (d : ℝ)
    (hd : |(q : ℝ) * d| ≤ 1 / 2) :
    1 / 4 ≤ Complex.normSq ((∑ j : Fin q, wave (d * j)) / q) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  by_cases hz : d = 0
  · subst d
    simp [wave, hq.ne']
    norm_num
  let z : ℂ := wave d
  let s : ℂ := ∑ j ∈ Finset.range q, z ^ j
  have he : (∑ j : Fin q, wave (d * j)) = s := by
    dsimp only [s]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [z]
    unfold wave
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hgeom : s * (z - 1) = z ^ q - 1 := geom_sum_mul z q
  have hpow : z ^ q = wave (q * d) := by
    dsimp [z]
    unfold wave
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hn := congrArg Complex.normSq hgeom
  rw [Complex.normSq_mul, hpow, wave_norm_sub, wave_norm_sub] at hn
  have hsine : 4 * ((q : ℝ) * d) ^ 2 ≤ Real.sin (π * ((q : ℝ) * d)) ^ 2 := by
    have h := Real.mul_le_sin
      (show 0 ≤ π * |(q : ℝ) * d| by positivity)
      (show π * |(q : ℝ) * d| ≤ π / 2 by nlinarith [Real.pi_pos])
    have hs : 2 * |(q : ℝ) * d| ≤ Real.sin (π * |(q : ℝ) * d|) := by
      convert h using 1 <;> field_simp
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * |(q : ℝ) * d|) hs 2
    rcases le_total 0 ((q : ℝ) * d) with ht | ht
    · rw [abs_of_nonneg ht] at hp
      nlinarith
    · rw [abs_of_nonpos ht, show π * -((q : ℝ) * d) = -(π * ((q : ℝ) * d)) by ring, Real.sin_neg] at hp
      nlinarith
  have hb : Real.sin (π * d) ^ 2 ≤ (π * d) ^ 2 := Real.sin_sq_le_sq
  have hprod := mul_le_mul_of_nonneg_left hb (Complex.normSq_nonneg s)
  have hp : π ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hz
  have hbound : (q : ℝ) ^ 2 / 4 ≤ Complex.normSq s := by
    nlinarith [mul_pos (sub_pos.mpr hp) hd2,
      mul_nonneg (Complex.normSq_nonneg s) (mul_nonneg (sub_nonneg.mpr hp.le) (sq_nonneg d))]
  rw [he, map_div₀, Complex.normSq_natCast]
  apply (le_div_iff₀ (by positivity : 0 < (q : ℝ) * q)).2
  nlinarith

private lemma weighted_cauchy (r : ℕ) (a u : Fin r → ℂ)
    (hu : ∀ k, ‖u k‖ = 1) :
    Complex.normSq (∑ k, u k * a k) ≤ (r : ℝ) * ∑ k, Complex.normSq (a k) := by
  have h : ‖∑ k, u k * a k‖ ≤ ∑ k, ‖a k‖ := by
    calc
      _ ≤ ∑ k, ‖u k * a k‖ := norm_sum_le _ _
      _ = _ := by simp [norm_mul, hu]
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hc := (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k : Fin r => ‖a k‖))
  simpa only [Complex.normSq_eq_norm_sq, Finset.card_univ, Fintype.card_fin] using hh.trans hc

private lemma sp_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) : act (A * B) x = act A (act B x) := by
  simp only [act, Matrix.mulVec_mulVec, WithLp.ofLp_toLp]

private lemma sp_kron {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ (ι × κ)) (a : ι) (b : κ) :
    act (Matrix.kronecker A (1 : Matrix κ κ ℂ)) x (a,b) = ∑ j, A a j * x (j,b) := by
  simp [act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

private lemma sp_amplitude (N : ℕ) (f : ℕ → ℕ)
    (b : Qubits (shorEll N)) (y : Qubits (Nat.clog 2 N)) :
    shorRunState N f (b,y) =
      (∑ a : Qubits (shorEll N),
        if natToBits (Nat.clog 2 N) (f (bitsToNat a)) = y
        then wave ((bitsToNat b : ℝ) * bitsToNat a / (2 : ℝ) ^ shorEll N) else 0) /
      (2 : ℂ) ^ shorEll N := by
  classical
  let m := Nat.clog 2 N
  let l := shorEll N
  let Q : Matrix (Qubits l × Qubits m) (Qubits l × Qubits m) ℂ :=
    Matrix.kronecker (qftQubits l) 1
  have hi (a : Qubits l) (v : Qubits m) :
      act Q (ket (0,0)) (a,v) =
        if v = 0 then (Real.sqrt ((2 : ℕ) ^ l) : ℂ)⁻¹ else 0 := by
    simp [Q, act, ket, Matrix.mulVec, dotProduct, qftQubits, qftMatrix,
      Matrix.one_apply, bitsEquivFin_apply, bitsToNat]
  have ho (a : Qubits l) (v : Qubits m) :
      act (xorOracle (fun a : Qubits l => natToBits m (f (bitsToNat a))))
        (act Q (ket (0,0))) (a,v) =
      if natToBits m (f (bitsToNat a)) = v
      then (Real.sqrt ((2 : ℕ) ^ l) : ℂ)⁻¹ else 0 := by
    change (∑ p : Qubits l × Qubits m,
      (if a = p.1 ∧ v = p.2 + natToBits m (f (bitsToNat p.1)) then (1 : ℂ) else 0) *
        act Q (ket (0,0)) p) = _
    simp only [Fintype.sum_prod_type, hi]
    simp [ite_and, eq_comm]
  unfold shorRunState
  rw [sp_mul, sp_mul, sp_kron]
  change (∑ a : Qubits l, qftQubits l b a *
    act (xorOracle (fun a : Qubits l => natToBits m (f (bitsToNat a))))
      (act Q (ket (0,0))) (a,y)) = _
  simp_rw [ho]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  change qftQubits l b a * (if natToBits m (f (bitsToNat a)) = y then
    (Real.sqrt ((2 : ℕ)^l) : ℂ)⁻¹ else 0) =
    (if natToBits m (f (bitsToNat a)) = y then
      wave ((bitsToNat b : ℝ) * bitsToNat a / (2 : ℝ)^l) else 0) / (2 : ℂ)^l
  by_cases hy : natToBits m (f (bitsToNat a)) = y
  · simp only [hy, ite_true]
    have hs : (Real.sqrt ((2 : ℕ) ^ l) : ℂ) ^ 2 = (2 : ℂ) ^ l := by
      norm_cast
      exact Real.sq_sqrt (Nat.cast_nonneg _)
    simp only [qftQubits, Matrix.submatrix_apply, qftMatrix, Matrix.of_apply,
      bitsEquivFin_apply, wave]
    push_cast at hs ⊢
    rw [show (Complex.exp (2 * (π : ℂ) * Complex.I * ((bitsToNat b : ℂ) * bitsToNat a) /
          (2 : ℂ) ^ l) / (Real.sqrt ((2 : ℝ) ^ l) : ℂ)) *
        (Real.sqrt ((2 : ℝ) ^ l) : ℂ)⁻¹ =
      Complex.exp (2 * π * Complex.I * ((bitsToNat b : ℂ) * bitsToNat a) / (2 : ℂ) ^ l) /
        (Real.sqrt ((2 : ℝ) ^ l) : ℂ)^2 by ring]
    rw [hs]
    congr 2
    push_cast
    ring
  · simp [hy]

private lemma bits_nat (n a : ℕ) (ha : a < 2 ^ n) :
    bitsToNat (natToBits n a) = a := by
  rw [← bitsEquivFin_apply]
  simp [natToBits, Nat.mod_eq_of_lt ha]

private lemma sp_labels (N r : ℕ) (hr : 0 < r) (hrN : r ≤ N)
    (f : ℕ → ℕ) (hf : ∀ a, f a < N) (hp : HasPeriod f r) :
    Function.Injective (fun k : Fin r => natToBits (Nat.clog 2 N) (f k)) ∧
    ∀ (a : ℕ) (k : Fin r),
      natToBits (Nat.clog 2 N) (f a) = natToBits (Nat.clog 2 N) (f k) ↔ a % r = k := by
  have hbits (a : ℕ) : f a < 2 ^ Nat.clog 2 N := (hf a).trans_le (Nat.le_pow_clog (by decide) _)
  have he (a b : ℕ) :
      natToBits (Nat.clog 2 N) (f a) = natToBits (Nat.clog 2 N) (f b) ↔ a % r = b % r := by
    constructor
    · intro h
      have heq := congrArg bitsToNat h
      rw [bits_nat _ _ (hbits a), bits_nat _ _ (hbits b)] at heq
      exact (hp a b).mp heq
    · intro h
      rw [(hp a b).mpr h]
  constructor
  · intro a b hab
    apply Fin.ext
    simpa only [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using (he a b).mp hab
  · intro a k
    simpa only [Nat.mod_eq_of_lt k.isLt] using he a k

private lemma wave_mod (c r a : ℕ) (hr : 0 < r) :
    wave (-((c : ℝ) / r) * a) = wave (-((c : ℝ) / r) * ((a % r : ℕ) : ℝ)) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have ha : (a : ℝ) = (a % r : ℕ) + (r : ℝ) * (a / r : ℕ) := by
    exact_mod_cast (Nat.mod_add_div a r).symm
  have he : -((c : ℝ) / r) * a =
      -((c : ℝ) / r) * ((a % r : ℕ) : ℝ) + (((-Int.ofNat (c * (a / r))) : ℤ) : ℝ) := by
    simp only [Int.ofNat_eq_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_mul, Nat.cast_mul]
    nth_rw 1 [ha]
    field_simp
    ring
  rw [he, wave_add, wave_int, mul_one]

private lemma sp_projection (N r c : ℕ) (hr : 0 < r) (hrN : r ≤ N)
    (f : ℕ → ℕ) (hf : ∀ a, f a < N) (hp : HasPeriod f r)
    (b : Qubits (shorEll N)) :
    (∑ k : Fin r, wave (-((c : ℝ) / r) * k) *
      shorRunState N f (b, natToBits (Nat.clog 2 N) (f k))) =
    (∑ a : Fin (2 ^ shorEll N),
      wave (((bitsToNat b : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r) * a)) /
      (2 : ℂ) ^ shorEll N := by
  classical
  have hl := (sp_labels N r hr hrN f hf hp).2
  simp_rw [sp_amplitude, ← mul_div_assoc]
  rw [← Finset.sum_div]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hh (a : Qubits (shorEll N)) :
      (∑ k : Fin r, wave (-((c : ℝ) / r) * k) *
        (if natToBits (Nat.clog 2 N) (f (bitsToNat a)) =
            natToBits (Nat.clog 2 N) (f k)
          then wave ((bitsToNat b : ℝ) * bitsToNat a / (2 : ℝ) ^ shorEll N) else 0)) =
      wave (((bitsToNat b : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r) * bitsToNat a) := by
    let k : Fin r := ⟨bitsToNat a % r, Nat.mod_lt _ hr⟩
    rw [Finset.sum_eq_single k]
    · rw [if_pos ((hl _ k).mpr rfl)]
      dsimp only [k]
      rw [← wave_mod c r (bitsToNat a) hr, ← wave_add]
      congr 1
      ring
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro he
      apply hj
      apply Fin.ext
      exact ((hl _ j).mp he).symm
    · simp
  simp_rw [hh]
  congr 1
  have he := (bitsEquivFin (shorEll N)).sum_comp
    (fun a : Fin (2 ^ shorEll N) =>
      wave (((bitsToNat b : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r) * a))
  simpa only [bitsEquivFin_apply] using he

private lemma sp_single_bin (N r c : ℕ) (hr : 0 < r) (hrN : r ≤ N)
    (f : ℕ → ℕ) (hf : ∀ a, f a < N) (hp : HasPeriod f r)
    (b : Qubits (shorEll N))
    (hb : |(bitsToNat b : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤
      1 / (2 * (2 : ℝ) ^ shorEll N)) :
    1 / (4 * (r : ℝ)) ≤ ∑ k : Fin r,
      Complex.normSq (shorRunState N f (b, natToBits (Nat.clog 2 N) (f k))) := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ shorEll N := by positivity
  have hd : |((2 ^ shorEll N : ℕ) : ℝ) *
      ((bitsToNat b : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r)| ≤ 1 / 2 := by
    push_cast
    rw [abs_mul, abs_of_pos hq]
    calc
      _ ≤ (2 : ℝ) ^ shorEll N * (1 / (2 * (2 : ℝ) ^ shorEll N)) :=
        mul_le_mul_of_nonneg_left hb hq.le
      _ = 1 / 2 := by field_simp
  have hlo := wave_sum_lower (2 ^ shorEll N) (by positivity) _ hd
  have hcs := weighted_cauchy r
    (fun k => shorRunState N f (b, natToBits (Nat.clog 2 N) (f k)))
    (fun k => wave (-((c : ℝ) / r) * k)) (fun k => wave_norm _)
  rw [sp_projection N r c hr hrN f hf hp b] at hcs
  push_cast at hlo
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * r)).2
  linarith [hlo.trans hcs]

private lemma rounded_bins (q r : ℕ) (hr : 0 < r) (hqr : r < q) :
    ∃ B : Fin r → Fin q, Function.Injective B ∧
      ∀ c : Fin r, |((B c : ℕ) : ℝ) / q - (c : ℕ) / (r : ℝ)| ≤ 1 / (2 * (q : ℝ)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (hr.trans hqr)
  have hqr0 : (r : ℝ) < q := by exact_mod_cast hqr
  let b (c : Fin r) : ℕ := ⌊(q : ℝ) * (c : ℕ) / r + 1 / 2⌋₊
  have hnear (c : Fin r) : |(b c : ℝ) - (q : ℝ) * (c : ℕ) / r| ≤ 1 / 2 := by
    have hlo := Nat.floor_le (show 0 ≤ (q : ℝ) * (c : ℕ) / r + 1 / 2 by positivity)
    have hhi := Nat.lt_floor_add_one ((q : ℝ) * (c : ℕ) / r + 1 / 2)
    exact abs_le.mpr ⟨by dsimp [b]; linarith, by dsimp [b]; linarith⟩
  have hbound (c : Fin r) : b c < q := by
    have hc : (c : ℝ) + 1 ≤ r := by exact_mod_cast c.isLt
    have hx : (q : ℝ) * (c : ℕ) / r + 1 ≤ q := by
      have hd : (q : ℝ) * (c : ℕ) / r ≤ (q : ℝ) - 1 := by
        apply (div_le_iff₀ hr0).2
        nlinarith
      linarith
    have hn := (abs_le.mp (hnear c)).2
    have : (b c : ℝ) < q := by linarith
    exact_mod_cast this
  let B (c : Fin r) : Fin q := ⟨b c, hbound c⟩
  have hinj : Function.Injective B := by
    intro c d he
    have he' : b c = b d := congrArg Fin.val he
    have hc := abs_le.mp (hnear c)
    have hd := abs_le.mp (hnear d)
    have hh : |(q : ℝ) * ((c : ℕ) - (d : ℕ) : ℝ)| ≤ r := by
      have hc1 := (div_le_iff₀ hr0).mp (show (q : ℝ) * (c : ℕ) / r ≤ (b c : ℝ) + 1/2 by linarith)
      have hc2 := (le_div_iff₀ hr0).mp (show (b c : ℝ) - 1/2 ≤ (q : ℝ) * (c : ℕ) / r by linarith)
      have hd1 := (div_le_iff₀ hr0).mp (show (q : ℝ) * (d : ℕ) / r ≤ (b d : ℝ) + 1/2 by linarith)
      have hd2 := (le_div_iff₀ hr0).mp (show (b d : ℝ) - 1/2 ≤ (q : ℝ) * (d : ℕ) / r by linarith)
      rw [he'] at hc1 hc2
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    apply Fin.ext
    rcases lt_trichotomy (c : ℕ) (d : ℕ) with h | h | h
    · have hc : (c : ℝ) + 1 ≤ d := by exact_mod_cast h
      have hl := (abs_le.mp hh).1
      nlinarith
    · exact h
    · have hc : (d : ℝ) + 1 ≤ c := by exact_mod_cast h
      have hl := (abs_le.mp hh).2
      nlinarith
  refine ⟨B, hinj, ?_⟩
  intro c
  have he : ((B c : ℕ) : ℝ) / q - (c : ℕ) / (r : ℝ) =
      ((b c : ℝ) - (q : ℝ) * (c : ℕ) / r) / q := by dsimp [B]; field_simp
  rw [he, abs_div, abs_of_pos hq0]
  calc
    _ ≤ (1 / 2) / (q : ℝ) := div_le_div_of_nonneg_right (hnear c) hq0.le
    _ = _ := by ring

theorem solution :
    ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℕ, 1 ≤ r → r ≤ N →
      ∀ f : ℕ → ℕ, (∀ t, f t < N) → HasPeriod f r →
        a * ((Nat.totient r : ℝ) / r) ≤ probEvent (shorRunState N f) (fun z =>
          ∃ c : ℕ, c < r ∧ Nat.Coprime c r ∧
            |(bitsToNat z.1 : ℝ) / (2 : ℝ) ^ shorEll N - (c : ℝ) / r| ≤
              1 / (2 * (2 : ℝ) ^ shorEll N)) := by
  classical
  refine ⟨1/4, by norm_num, 1, ?_⟩
  intro N hN r hr hrN f hf hp
  have hr0 : 0 < r := hr
  have hqr : r < 2 ^ shorEll N := by
    have hclog := Nat.le_pow_clog (by decide : 1 < 2) (N^2+1)
    change N^2+1 ≤ 2 ^ shorEll N at hclog
    nlinarith
  obtain ⟨B, hB, hnear⟩ := rounded_bins (2 ^ shorEll N) r hr0 hqr
  let bb (c : Fin r) : Qubits (shorEll N) := (bitsEquivFin (shorEll N)).symm (B c)
  let yy (k : Fin r) : Qubits (Nat.clog 2 N) := natToBits (Nat.clog 2 N) (f k)
  have hbn (c : Fin r) : bitsToNat (bb c) = (B c : ℕ) := by
    rw [← bitsEquivFin_apply]
    simp [bb]
  have hbb : Function.Injective bb :=
    (bitsEquivFin (shorEll N)).symm.injective.comp hB
  have hyy : Function.Injective yy := (sp_labels N r hr0 hrN f hf hp).1
  let good : Finset (Fin r) := Finset.univ.filter fun c => Nat.Coprime (c : ℕ) r
  have hcount : good.card = Nat.totient r := by
    dsimp only [good]
    rw [Nat.totient_eq_card_coprime]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact (Fin.sum_univ_eq_sum_range
      (fun c : ℕ => if c.Coprime r then (1 : ℕ) else 0) r).trans (by simp only [Nat.coprime_comm])
  have hbin (c : Fin r) :
      1 / (4 * (r : ℝ)) ≤ ∑ k : Fin r, Complex.normSq (shorRunState N f (bb c, yy k)) := by
    apply sp_single_bin N r c hr0 hrN f hf hp (bb c)
    rw [hbn]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnear c
  let Z (p : Fin r × Fin r) : Qubits (shorEll N) × Qubits (Nat.clog 2 N) :=
    (bb p.1, yy p.2)
  have hZ : Function.Injective Z := by
    intro a b he
    exact Prod.ext (hbb (congrArg Prod.fst he)) (hyy (congrArg Prod.snd he))
  let S : Finset (Fin r × Fin r) := good ×ˢ Finset.univ
  let E := fun z : Qubits (shorEll N) × Qubits (Nat.clog 2 N) =>
    ∃ c : ℕ, c < r ∧ Nat.Coprime c r ∧
      |(bitsToNat z.1 : ℝ) / (2 : ℝ)^shorEll N - (c : ℝ)/r| ≤
        1 / (2 * (2 : ℝ)^shorEll N)
  have hsub : S.image Z ⊆ Finset.univ.filter E := by
    intro z hz
    obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hz
    have hc : Nat.Coprime (p.1 : ℕ) r := (Finset.mem_filter.mp (Finset.mem_product.mp hpS).1).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, p.1, p.1.isLt, hc, ?_⟩
    change |(bitsToNat (bb p.1) : ℝ) / (2 : ℝ)^shorEll N - (p.1 : ℕ)/ (r : ℝ)| ≤ _
    rw [hbn]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnear p.1
  have htotal :
      (good.card : ℝ) * (1 / (4 * (r : ℝ))) ≤
        ∑ z ∈ Finset.univ.filter E, Complex.normSq (shorRunState N f z) := by
    calc
      _ = ∑ c ∈ good, (1 / (4 * (r : ℝ))) := by simp
      _ ≤ ∑ c ∈ good, ∑ k : Fin r, Complex.normSq (shorRunState N f (bb c, yy k)) :=
        Finset.sum_le_sum (fun c _ => hbin c)
      _ = ∑ p ∈ S, Complex.normSq (shorRunState N f (Z p)) := by
        simp [S, Z, Finset.sum_product]
      _ = ∑ z ∈ S.image Z, Complex.normSq (shorRunState N f z) :=
        (Finset.sum_image (f := fun z => Complex.normSq (shorRunState N f z))
          (s := S) (g := Z) hZ.injOn).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Complex.normSq_nonneg _)
  rw [hcount] at htotal
  have he : (1 / 4 : ℝ) * ((Nat.totient r : ℝ) / r) =
      (Nat.totient r : ℝ) * (1 / (4 * (r : ℝ))) := by ring
  rw [he]
  convert htotal using 1
  simp only [E, probEvent, prob, ket, EuclideanSpace.inner_single_left, map_one,
    one_mul, Complex.normSq_eq_norm_sq]
