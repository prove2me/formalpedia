-- Prove2me | solution 1 for ShorWiki.order_finding_succeeds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T16:02:09.958188+00:00
-- url     : https://prove2.me/submissions/5d944804-428d-4f0b-b602-1cc1bcbe6e06

import Mathlib
import Definitions.Def_ShorWiki_Defs
open ShorWiki

namespace ShorGate

/-- The basis permutation underlying `mulModGate`. -/
def sig (N a n : ℕ) (hN : N ≤ 2 ^ n) (k : Fin (2 ^ n)) : Fin (2 ^ n) :=
  if h : (k : ℕ) < N then ⟨a * k % N, lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hN⟩ else k

lemma sig_lt (N a n : ℕ) (hN : N ≤ 2 ^ n) (k : Fin (2 ^ n)) (hk : (k : ℕ) < N) :
    ((sig N a n hN k : Fin (2 ^ n)) : ℕ) = a * k % N := by
  unfold sig; rw [dif_pos hk]

lemma sig_ge (N a n : ℕ) (hN : N ≤ 2 ^ n) (k : Fin (2 ^ n)) (hk : N ≤ (k : ℕ)) :
    sig N a n hN k = k := by
  unfold sig; rw [dif_neg (by omega)]

lemma gate_eq (N a n : ℕ) (hN : N ≤ 2 ^ n) (i k : Fin (2 ^ n)) :
    mulModGate N a n i k = if i = sig N a n hN k then 1 else 0 := by
  unfold mulModGate sig
  split_ifs <;> simp_all [Fin.ext_iff]

lemma gate_pow (N a n : ℕ) (hN : N ≤ 2 ^ n) (m : ℕ) (i k : Fin (2 ^ n)) :
    (mulModGate N a n ^ m) i k = if i = (sig N a n hN)^[m] k then 1 else 0 := by
  induction m generalizing i with
  | zero => rw [pow_zero, Matrix.one_apply]; rfl
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [gate_eq N a n hN, ih]
    rw [Finset.sum_eq_single ((sig N a n hN)^[m] k)]
    · rw [Function.iterate_succ_apply']; simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma iterate_sig (N a n : ℕ) (hN : N ≤ 2 ^ n) (m : ℕ) (k : Fin (2 ^ n)) (hk : (k : ℕ) < N) :
    (((sig N a n hN)^[m] k : Fin (2 ^ n)) : ℕ) = a ^ m * k % N := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt hk]
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have hlt : (((sig N a n hN)^[m] k : Fin (2 ^ n)) : ℕ) < N := by
      rw [ih]; exact Nat.mod_lt _ (by omega)
    rw [sig_lt N a n hN _ hlt, ih, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]; ring_nf

lemma iterate_sig_ge (N a n : ℕ) (hN : N ≤ 2 ^ n) (m : ℕ) (k : Fin (2 ^ n)) (hk : N ≤ (k : ℕ)) :
    (sig N a n hN)^[m] k = k := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, sig_ge N a n hN k hk]

theorem gate_pow_ord (N a : ℕ) (ha : 1 < a) (haN : a < N) :
    mulModGate N a (regBits N) ^ ord N a = 1 := by
  have hN : N ≤ 2 ^ regBits N := Nat.le_pow_clog (by norm_num) N
  have hpow : a ^ ord N a % N = 1 := by
    have h := pow_orderOf_eq_one (a : ZMod N)
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at h
    unfold ord; rw [h, Nat.mod_eq_of_lt (by omega)]
  ext i k
  rw [gate_pow N a _ hN, Matrix.one_apply]
  congr 1
  apply propext
  suffices hfix : (sig N a (regBits N) hN)^[ord N a] k = k by rw [hfix]
  by_cases hk : (k : ℕ) < N
  · apply Fin.ext
    rw [iterate_sig N a _ hN _ k hk, Nat.mul_mod, hpow, one_mul, Nat.mod_mod,
      Nat.mod_eq_of_lt hk]
  · exact iterate_sig_ge N a _ hN _ k (by omega)

end ShorGate

namespace ShorGate

lemma ord_pos (N a : ℕ) (haN : a < N) (hcop : Nat.Coprime a N) : 0 < ord N a := by
  have : NeZero N := ⟨by omega⟩
  unfold ord
  have : orderOf (ZMod.unitOfCoprime a hcop) = orderOf (a : ZMod N) := by
    rw [← orderOf_units]; rfl
  rw [← this]
  exact orderOf_pos _

lemma pow_mod_ne_one (N a k : ℕ) (hk0 : 0 < k) (hk : k < ord N a) (hN : 1 < N) :
    a ^ k % N ≠ 1 := by
  intro h
  have h' : ((a ^ k : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by
    rw [ZMod.natCast_eq_natCast_iff', h, Nat.mod_eq_of_lt hN]
  push_cast at h'
  have := orderOf_dvd_of_pow_eq_one h'
  have := Nat.le_of_dvd hk0 this
  unfold ord at hk; omega

end ShorGate

open Matrix

namespace ShorGate
theorem eigvec (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (j : ℕ) :
    eigState N a (regBits N) j ≠ 0 ∧
      mulModGate N a (regBits N) *ᵥ eigState N a (regBits N) j
        = omega (ord N a) ^ j • eigState N a (regBits N) j := by
  have hN : N ≤ 2 ^ regBits N := Nat.le_pow_clog (by norm_num) N
  set r := ord N a with hr
  have hr0 : 0 < r := ord_pos N a haN hcop
  have hprim : IsPrimitiveRoot (omega r) r := Complex.isPrimitiveRoot_exp r hr0.ne'
  have hω0 : omega r ≠ 0 := hprim.ne_zero hr0.ne'
  have hpow : a ^ r % N = 1 := by
    have h := pow_orderOf_eq_one (a : ZMod N)
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at h
    rw [hr]; unfold ord; rw [h, Nat.mod_eq_of_lt (by omega)]
  set c : ℂ := (1 / Real.sqrt r : ℂ) with hc
  have hc0 : c ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr (by exact_mod_cast hr0)
    rw [hc]; simp only [one_div, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]; exact this.ne'
  constructor
  · -- the component at index 1 equals c
    intro h0
    have h1 : 1 < 2 ^ regBits N := lt_of_lt_of_le (by omega) hN
    have := congrFun h0 ⟨1, h1⟩
    simp only [eigState, Pi.zero_apply, ← hr] at this
    rw [Finset.sum_eq_single 0] at this
    · simp only [zero_mul, pow_zero, inv_one, one_mul, Nat.mod_eq_of_lt (show 1 < N by omega),
        if_true] at this
      rw [← hc] at this
      simp at this
      exact hc0 (by simpa using this)
    · intro k hk hk0
      have := pow_mod_ne_one N a k (Nat.pos_of_ne_zero hk0) (Finset.mem_range.mp hk) (by omega)
      rw [if_neg (Ne.symm this), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr hr0) h
  · funext i
    simp only [Matrix.mulVec, dotProduct, gate_eq N a _ hN, eigState, Pi.smul_apply, smul_eq_mul,
      ← hr]
    set f : ℕ → ℂ := fun k => (omega r ^ (k * j))⁻¹ * if (i : ℕ) = a ^ k % N then 1 else 0 with hf
    have hcol : ∀ k : ℕ, (∑ x : Fin (2 ^ regBits N),
        (if i = sig N a (regBits N) hN x then (1 : ℂ) else 0) *
          ((omega r ^ (k * j))⁻¹ * if (x : ℕ) = a ^ k % N then 1 else 0)) = omega r ^ j * f (k + 1) := by
      intro k
      have hm : a ^ k % N < 2 ^ regBits N := lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hN
      rw [Finset.sum_eq_single ⟨a ^ k % N, hm⟩]
      · have hs : ((sig N a (regBits N) hN ⟨a ^ k % N, hm⟩ : Fin _) : ℕ) = a ^ (k + 1) % N := by
          rw [sig_lt N a _ hN _ (Nat.mod_lt _ (by omega))]
          simp only
          rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ, mul_comm]
        have hw : (omega r ^ (k * j))⁻¹ = omega r ^ j * (omega r ^ ((k + 1) * j))⁻¹ := by
          rw [add_mul, one_mul, pow_add]; field_simp
        simp only [hf, if_true, mul_one, Fin.ext_iff, hs, hw]
        split_ifs <;> ring
      · intro b _ hb
        have : (b : ℕ) ≠ a ^ k % N := fun h => hb (Fin.ext h)
        rw [if_neg this]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    have lhs : (∑ x : Fin (2 ^ regBits N),
        (if i = sig N a (regBits N) hN x then (1 : ℂ) else 0) *
          (1 / ↑√↑r * ∑ k ∈ Finset.range r,
            (omega r ^ (k * j))⁻¹ * if (x : ℕ) = a ^ k % N then 1 else 0)) =
        1 / ↑√↑r * ∑ k ∈ Finset.range r, omega r ^ j * f (k + 1) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hcol k, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [lhs, ← Finset.mul_sum]
    have hfr : f r = f 0 := by
      simp only [hf, zero_mul, pow_zero, inv_one, hpow, Nat.mod_eq_of_lt (show 1 < N by omega)]
      rw [pow_mul, hprim.pow_eq_one, one_pow, inv_one]
    have hshift : ∑ k ∈ Finset.range r, f (k + 1) = ∑ k ∈ Finset.range r, f k := by
      have h1 := Finset.sum_range_succ f r
      have h2 := Finset.sum_range_succ' f r
      rw [hfr] at h1
      linear_combination h1 - h2
    rw [hshift]
    ring

end ShorGate
open ShorWiki Matrix Kronecker

namespace ShorPE

lemma kron_mulVec {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ)
    (u : Fin d₁ → ℂ) (v : Fin d₂ → ℂ) :
    (A ⊗ₖ B) *ᵥ tensorState u v = tensorState (A *ᵥ u) (B *ᵥ v) := by
  funext p
  simp only [mulVec, dotProduct, kroneckerMap_apply, tensorState, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  ring

lemma hadamard_zero (m : ℕ) :
    hadamardTensor m *ᵥ ket (2 ^ m) 0 = fun _ => (1 / Real.sqrt (2 ^ m) : ℂ) := by
  funext x
  simp only [mulVec, dotProduct, ket]
  rw [Finset.sum_eq_single ⟨0, by positivity⟩]
  · simp [hadamardTensor]
  · intro b _ hb
    have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma pow_mulVec_eig {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) (μ : ℂ)
    (h : U *ᵥ ψ = μ • ψ) (k : ℕ) : (U ^ k) *ᵥ ψ = μ ^ k • ψ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

/-- phase picked up at bit `b` -/
noncomputable def ph (μ : ℂ) (b x : ℕ) : ℂ := if x.testBit b then μ ^ (2 ^ b) else 1

lemma ctrl_gate (N a n m b : ℕ) (ψ : Fin (2 ^ n) → ℂ) (μ : ℂ)
    (h : mulModGate N a n *ᵥ ψ = μ • ψ) (f : Fin (2 ^ m) → ℂ) :
    controlledPowGate N a n m b *ᵥ tensorState f ψ
      = tensorState (fun x => ph μ b x * f x) ψ := by
  have hp := pow_mulVec_eig _ ψ μ h (2 ^ b)
  funext p
  simp only [mulVec, dotProduct, controlledPowGate, tensorState, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single p.1]
  · simp only [if_true]
    unfold ph
    split_ifs with hb
    · have := congrFun hp p.2
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [mul_comm (μ ^ 2 ^ b) (f p.1), mul_assoc, ← this, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_); ring
    · rw [Finset.sum_eq_single p.2]
      · simp
      · intro y _ hy; rw [one_apply_ne (Ne.symm hy)]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
  · intro x _ hx
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [if_neg (Ne.symm hx)]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

lemma ctrl_list (N a n m : ℕ) (ψ : Fin (2 ^ n) → ℂ) (μ : ℂ)
    (h : mulModGate N a n *ᵥ ψ = μ • ψ) (L : List ℕ) (f : Fin (2 ^ m) → ℂ) :
    (L.map (fun b => controlledPowGate N a n m b)).prod *ᵥ tensorState f ψ
      = tensorState (fun x => (L.map (fun b => ph μ b x)).prod * f x) ψ := by
  induction L generalizing f with
  | nil => simp
  | cons b L ih =>
    rw [List.map_cons, List.prod_cons, ← mulVec_mulVec, ih, ctrl_gate N a n m b ψ μ h]
    congr 1; funext x; simp only [List.map_cons, List.prod_cons]; ring

lemma prod_ph (μ : ℂ) (m : ℕ) : ∀ x : ℕ, x < 2 ^ m →
    ((List.range m).map (fun b => ph μ b x)).prod = μ ^ x := by
  induction m with
  | zero => intro x hx; simp at hx; subst hx; simp
  | succ m ih =>
    intro x hx
    rw [List.range_succ, List.map_append, List.prod_append]
    have e1 : (List.range m).map (fun b => ph μ b x) = (List.range m).map (fun b => ph μ b (x % 2 ^ m)) := by
      refine List.map_congr_left (fun b hb => ?_)
      have hb' : b < m := List.mem_range.1 hb
      unfold ph; rw [Nat.testBit_mod_two_pow]; simp [hb']
    rw [e1, ih (x % 2 ^ m) (Nat.mod_lt _ (by positivity))]
    have hq : x / 2 ^ m < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hx; linarith
    have ht : x.testBit m = decide (x / 2 ^ m = 1) := by
      have := Nat.testBit_div_two_pow (n := m) x 0
      rw [zero_add] at this
      rw [← this, Nat.testBit_zero, Nat.mod_eq_of_lt hq]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    unfold ph
    rw [ht]
    have hx' : x = x % 2 ^ m + 2 ^ m * (x / 2 ^ m) := (Nat.mod_add_div x (2 ^ m)).symm
    by_cases h1 : x / 2 ^ m = 1
    · simp only [h1, decide_true, if_true]
      rw [← pow_add]; congr 1; rw [h1, mul_one] at hx'; omega
    · have h0 : x / 2 ^ m = 0 := by
        generalize x / 2 ^ m = q at hq h1 ⊢; omega
      simp only [h1, decide_false, Bool.false_eq_true, if_false, mul_one]
      congr 1; rw [h0, mul_zero, add_zero] at hx'; omega

lemma circuit_eig (N a n m : ℕ) (ψ : Fin (2 ^ n) → ℂ) (μ : ℂ)
    (h : mulModGate N a n *ᵥ ψ = μ • ψ) :
    phaseEstimationCircuit N a n m *ᵥ tensorState (ket (2 ^ m) 0) ψ
      = tensorState (qftInv m *ᵥ fun x => (1 / Real.sqrt (2 ^ m) : ℂ) * μ ^ (x : ℕ)) ψ := by
  unfold phaseEstimationCircuit controlledPowers
  rw [← mulVec_mulVec, ← mulVec_mulVec, kron_mulVec, hadamard_zero, one_mulVec,
    ctrl_list N a n m ψ μ h, kron_mulVec, one_mulVec]
  congr 2
  funext x
  rw [prod_ph μ m x x.isLt]; ring


lemma norm_exp_sub_one (θ : ℝ) : ‖Complex.exp (θ * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have h : Complex.exp (θ * Complex.I) - 1
      = Complex.exp ((θ / 2 : ℝ) * Complex.I) * (2 * Complex.I * (Real.sin (θ / 2) : ℂ)) := by
    have e : Complex.exp (θ * Complex.I) = Complex.exp ((θ / 2 : ℝ) * Complex.I) * Complex.exp ((θ / 2 : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [Complex.ofReal_sin, Complex.sin, e]
    have e2 : Complex.exp ((θ / 2 : ℝ) * Complex.I) * Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]; ring_nf; simp
    generalize Complex.exp ((θ / 2 : ℝ) * Complex.I) = u at e2 ⊢
    generalize Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) = v at e2 ⊢
    linear_combination e2 + (-(u * (v - u))) * Complex.I_sq
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs]
  simp

lemma geom_bound (M : ℕ) (hM : 1 ≤ M) (δ : ℝ) (hδ : |δ| ≤ 1 / (2 * M)) :
    2 / Real.pi ≤ ‖(1 / (M : ℂ)) * ∑ x ∈ Finset.range M, Complex.exp ((2 * Real.pi * δ : ℝ) * Complex.I) ^ x‖ := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hpi := Real.pi_pos
  by_cases h0 : δ = 0
  · subst h0
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [one_div, inv_mul_cancel₀ (by exact_mod_cast (show M ≠ 0 by omega)), norm_one]
    rw [div_le_one hpi]; linarith [Real.pi_gt_three]
  set z := Complex.exp ((2 * Real.pi * δ : ℝ) * Complex.I) with hz
  have hδ' : 0 < |δ| := abs_pos.2 h0
  have hzM : z ^ M = Complex.exp ((2 * Real.pi * M * δ : ℝ) * Complex.I) := by
    rw [hz, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hn1 : ‖z - 1‖ = 2 * |Real.sin (Real.pi * δ)| := by
    rw [hz, norm_exp_sub_one]; congr 2; ring
  have hnM : ‖z ^ M - 1‖ = 2 * |Real.sin (Real.pi * M * δ)| := by
    rw [hzM, norm_exp_sub_one]; congr 2; ring
  -- bounds on sines
  have hA : 2 * M * |δ| ≤ |Real.sin (Real.pi * M * δ)| := by
    have hx0 : 0 ≤ Real.pi * M * |δ| := by positivity
    have hx1 : Real.pi * M * |δ| ≤ Real.pi / 2 := by
      have : M * |δ| ≤ 1 / 2 := by
        have := mul_le_mul_of_nonneg_left hδ hM0.le
        rw [show (M : ℝ) * (1 / (2 * M)) = 1 / 2 by field_simp] at this; exact this
      nlinarith
    have := Real.mul_le_sin hx0 hx1
    have hsp : 0 ≤ Real.sin (Real.pi * M * |δ|) := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith)
    have e : |Real.sin (Real.pi * M * δ)| = Real.sin (Real.pi * M * |δ|) := by
      rcases abs_cases δ with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1] at hsp ⊢; rw [abs_of_nonneg hsp]
      · have : Real.sin (Real.pi * M * δ) = -Real.sin (Real.pi * M * |δ|) := by
          rw [h1, mul_neg, Real.sin_neg, neg_neg]
        rw [this, abs_neg, abs_of_nonneg hsp]
    rw [e]
    calc 2 * M * |δ| = 2 / Real.pi * (Real.pi * M * |δ|) := by field_simp
      _ ≤ _ := this
  have hB : |Real.sin (Real.pi * δ)| ≤ Real.pi * |δ| := by
    have := Real.abs_sin_le_abs (x := Real.pi * δ)
    rwa [abs_mul, abs_of_pos hpi] at this
  have hsin0 : 0 < |Real.sin (Real.pi * δ)| := by
    apply abs_pos.2
    intro hs
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have : |Real.sin (Real.pi * M * δ)| ≤ M * |Real.sin (Real.pi * δ)| := by
      -- |sin(M y)| ≤ M |sin y|
      have key : ∀ k : ℕ, |Real.sin (k * (Real.pi * δ))| ≤ k * |Real.sin (Real.pi * δ)| := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          push_cast
          rw [add_mul, one_mul, Real.sin_add]
          calc |Real.sin (k * (Real.pi * δ)) * Real.cos (Real.pi * δ) + Real.cos (k * (Real.pi * δ)) * Real.sin (Real.pi * δ)|
              ≤ |Real.sin (k * (Real.pi * δ))| * 1 + 1 * |Real.sin (Real.pi * δ)| := by
                refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
                · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
                · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
            _ ≤ (k + 1) * |Real.sin (Real.pi * δ)| := by linarith
      have := key M
      rwa [show (M : ℝ) * (Real.pi * δ) = Real.pi * M * δ by ring] at this
    rw [hs, abs_zero, mul_zero] at this
    have : 2 * M * |δ| ≤ 0 := hA.trans this
    have : 0 < 2 * M * |δ| := by positivity
    linarith
  have hz1 : z ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hn1; linarith
  rw [geom_sum_eq hz1, norm_mul, norm_div, norm_div, hnM, hn1, norm_one, Complex.norm_natCast]
  rw [show 1 / (M : ℝ) * (2 * |Real.sin (Real.pi * M * δ)| / (2 * |Real.sin (Real.pi * δ)|))
      = |Real.sin (Real.pi * M * δ)| / (M * |Real.sin (Real.pi * δ)|) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  calc 2 / Real.pi * (M * |Real.sin (Real.pi * δ)|) ≤ 2 / Real.pi * (M * (Real.pi * |δ|)) := by gcongr
    _ = 2 * M * |δ| := by field_simp
    _ ≤ _ := hA

end ShorPE
open ShorWiki Matrix Kronecker

namespace ShorPE

lemma phi_eq (m r j : ℕ) (hr : 0 < r) (k : Fin (2 ^ m)) :
    (qftInv m *ᵥ fun x => (1 / Real.sqrt (2 ^ m) : ℂ) * (omega r ^ j) ^ (x : ℕ)) k
      = (1 / ((2 ^ m : ℕ) : ℂ)) * ∑ x ∈ Finset.range (2 ^ m),
          Complex.exp ((2 * Real.pi * ((j : ℝ) / r - (k : ℕ) / 2 ^ m) : ℝ) * Complex.I) ^ x := by
  simp only [mulVec, dotProduct]
  rw [Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun x => (1 / ((2 ^ m : ℕ) : ℂ)) *
    Complex.exp ((2 * Real.pi * ((j : ℝ) / r - (k : ℕ) / 2 ^ m) : ℝ) * Complex.I) ^ x)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hM : (0 : ℝ) < 2 ^ m := by positivity
  have hsq : ((Real.sqrt (2 ^ m) : ℝ) : ℂ) * ((Real.sqrt (2 ^ m) : ℝ) : ℂ) = ((2 ^ m : ℕ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hM.le]; push_cast; ring
  have hs0 : ((Real.sqrt (2 ^ m) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (2 ^ m) := Real.sqrt_pos.2 hM
    exact_mod_cast this.ne'
  simp only [qftInv, qft, conjTranspose_apply, star_mul', Complex.star_def, map_div₀, map_one,
    Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  have hω : (omega r ^ j) ^ (x : ℕ) = Complex.exp (2 * Real.pi * Complex.I * j * (x : ℕ) / r) := by
    unfold omega
    rw [← pow_mul, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hω, ← Complex.exp_nat_mul]
  have hconj : (starRingEnd ℂ) (2 * ↑Real.pi * Complex.I * ↑(k : ℕ) * ↑(x : ℕ) / 2 ^ m)
      = -(2 * ↑Real.pi * Complex.I * ↑(x : ℕ) * ↑(k : ℕ) / 2 ^ m) := by
    simp only [map_div₀, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
    ring
  rw [hconj]
  have e : Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑(x : ℕ) * ↑(k : ℕ) / 2 ^ m)) *
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑j * ↑(x : ℕ) / ↑r)
      = Complex.exp (↑(x : ℕ) * (↑(2 * Real.pi * ((j : ℝ) / r - (k : ℕ) / 2 ^ m)) * Complex.I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← e]
  field_simp
  rw [sq, hsq]


theorem phase_est (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (j : ℕ) (hj : j < ord N a) :
    ∃ φ : Fin (2 ^ (2 * regBits N)) → ℂ,
      phaseEstimationCircuit N a (regBits N) (2 * regBits N) *ᵥ
          tensorState (ket (2 ^ (2 * regBits N)) 0) (eigState N a (regBits N) j)
        = tensorState φ (eigState N a (regBits N) j) ∧
      ∀ k : Fin (2 ^ (2 * regBits N)),
        |((k : ℕ) : ℝ) / 2 ^ (2 * regBits N) - (j : ℝ) / ord N a|
            ≤ 1 / 2 ^ (2 * regBits N + 1) →
          4 / Real.pi ^ 2 ≤ ‖φ k‖ ^ 2 := by
  set m := 2 * regBits N with hm
  set r := ord N a with hr
  have hr0 : 0 < r := ShorGate.ord_pos N a haN hcop
  have heig := (ShorGate.eigvec N a ha haN hcop j).2
  refine ⟨_, circuit_eig N a (regBits N) m _ _ heig, fun k hk => ?_⟩
  rw [phi_eq m r j hr0 k]
  have hb := geom_bound (2 ^ m) (Nat.one_le_two_pow) ((j : ℝ) / r - (k : ℕ) / 2 ^ m) (by
    rw [abs_sub_comm]; push_cast
    calc _ ≤ 1 / 2 ^ (m + 1) := hk
      _ = 1 / (2 * 2 ^ m) := by rw [pow_succ, mul_comm])
  have h2 : 0 ≤ 2 / Real.pi := by positivity
  have := pow_le_pow_left₀ h2 hb 2
  rw [div_pow] at this
  push_cast at this ⊢
  linarith

end ShorPE
open ShorWiki

namespace ShorSumEig

lemma inner_sum (r k : ℕ) (hr : 0 < r) (hk : k < r) :
    ∑ j ∈ Finset.range r, (omega r ^ (k * j))⁻¹ = if k = 0 then (r : ℂ) else 0 := by
  have hprim : IsPrimitiveRoot (omega r) r := Complex.isPrimitiveRoot_exp r hr.ne'
  split_ifs with hk0
  · subst hk0; simp
  · set x := (omega r)⁻¹ ^ k with hx
    have hprim' := hprim.inv
    have hx1 : x ≠ 1 := by
      intro h
      have := (hprim'.pow_eq_one_iff_dvd k).mp h
      have := Nat.le_of_dvd (by omega) this
      omega
    have hxr : x ^ r = 1 := by
      rw [hx, ← pow_mul, mul_comm, pow_mul, hprim'.pow_eq_one, one_pow]
    have e : ∑ j ∈ Finset.range r, (omega r ^ (k * j))⁻¹ = ∑ j ∈ Finset.range r, x ^ j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hx, ← inv_pow, ← pow_mul]
    rw [e]
    have hg := geom_sum_mul x r
    rw [hxr, sub_self] at hg
    rcases mul_eq_zero.mp hg with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hx1

lemma ord_pos (N a : ℕ) (haN : a < N) (hcop : Nat.Coprime a N) : 0 < ord N a := by
  have : NeZero N := ⟨by omega⟩
  unfold ord
  have : orderOf (ZMod.unitOfCoprime a hcop) = orderOf (a : ZMod N) := by
    rw [← orderOf_units]; rfl
  rw [← this]
  exact orderOf_pos _

end ShorSumEig

namespace ShorSumEig
theorem ket_one (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) :
    (1 / Real.sqrt (ord N a) : ℂ) • ∑ j ∈ Finset.range (ord N a), eigState N a (regBits N) j
      = ket (2 ^ regBits N) 1 := by
  set r := ord N a with hr
  have hr0 : 0 < r := ord_pos N a haN hcop
  have hsq : ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) = r := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have hsq0 : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr (by exact_mod_cast hr0)
    exact_mod_cast this.ne'
  have h1N : 1 % N = 1 := Nat.mod_eq_of_lt (by omega)
  funext i
  simp only [Pi.smul_apply, Finset.sum_apply, eigState, smul_eq_mul, ket]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← hr]
  have hin : ∀ y ∈ Finset.range r, (∑ x ∈ Finset.range r,
      (omega r ^ (y * x))⁻¹ * if (i : ℕ) = a ^ y % N then (1 : ℂ) else 0) =
      (if y = 0 then (r : ℂ) else 0) * if (i : ℕ) = a ^ y % N then (1 : ℂ) else 0 := by
    intro y hy
    rw [← Finset.sum_mul, inner_sum r y hr0 (Finset.mem_range.mp hy)]
  rw [Finset.sum_congr rfl hin]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range, if_pos hr0, pow_zero, h1N]
  split_ifs
  · field_simp
    rw [sq, hsq]
  · simp

end ShorSumEig
open ShorWiki Matrix Kronecker

namespace ShorPE

lemma s_inj (N a : ℕ) (haN : a < N) (hcop : Nat.Coprime a N) (k k' : ℕ) (hk : k < ord N a)
    (hk' : k' < ord N a) (h : a ^ k % N = a ^ k' % N) : k = k' := by
  have h' : ((a : ZMod N)) ^ k = ((a : ZMod N)) ^ k' := by
    have := (ZMod.natCast_eq_natCast_iff' (a ^ k) (a ^ k') N).2 h
    push_cast at this; exact this
  exact pow_injOn_Iio_orderOf hk hk' h'

lemma omega_conj (r : ℕ) : (starRingEnd ℂ) (omega r) = (omega r)⁻¹ := by
  unfold omega
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  ring

lemma omega_ne (r : ℕ) (hr : 0 < r) : omega r ≠ 0 := Complex.exp_ne_zero _

lemma geom_ortho (r j l : ℕ) (hr : 0 < r) (hj : j < r) (hl : l < r) :
    ∑ k ∈ Finset.range r, (omega r ^ (k * j))⁻¹ * (starRingEnd ℂ) ((omega r ^ (k * l))⁻¹)
      = if j = l then (r : ℂ) else 0 := by
  have hprim : IsPrimitiveRoot (omega r) r := Complex.isPrimitiveRoot_exp r hr.ne'
  have hω0 := omega_ne r hr
  set x := (omega r)⁻¹ ^ j * omega r ^ l with hx
  have e : ∀ k, (omega r ^ (k * j))⁻¹ * (starRingEnd ℂ) ((omega r ^ (k * l))⁻¹) = x ^ k := by
    intro k
    rw [map_inv₀, map_pow, omega_conj, hx, mul_pow, ← pow_mul, ← pow_mul, inv_pow, inv_pow, inv_inv,
      ← inv_pow]
    ring_nf
  simp_rw [e]
  split_ifs with hjl
  · subst hjl
    have : x = 1 := by rw [hx, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hω0)]
    simp [this]
  · have hx1 : x ≠ 1 := by
      intro h
      rw [hx, inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ hω0)] at h
      have := hprim.pow_inj hj hl h
      exact hjl this
    have hxr : x ^ r = 1 := by
      rw [hx, mul_pow, ← pow_mul, ← pow_mul, inv_pow, mul_comm j r, mul_comm l r, pow_mul, pow_mul,
        hprim.pow_eq_one]; simp
    have hg := geom_sum_mul x r
    rw [hxr, sub_self] at hg
    rcases mul_eq_zero.mp hg with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hx1

lemma ortho (N a : ℕ) (ha : 1 < a) (haN : a < N) (hcop : Nat.Coprime a N) (j l : ℕ)
    (hj : j < ord N a) (hl : l < ord N a) :
    ∑ i, eigState N a (regBits N) j i * (starRingEnd ℂ) (eigState N a (regBits N) l i)
      = if j = l then 1 else 0 := by
  have hN : N ≤ 2 ^ regBits N := Nat.le_pow_clog (by norm_num) N
  set r := ord N a with hr
  have hr0 : 0 < r := ShorGate.ord_pos N a haN hcop
  set c : ℂ := (1 / Real.sqrt r : ℂ) with hc
  have hcc : c * (starRingEnd ℂ) c = 1 / r := by
    rw [hc, map_div₀, map_one, Complex.conj_ofReal]
    have hsq : ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) = r := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
    rw [div_mul_div_comm, one_mul, hsq]
  simp only [eigState, ← hr, map_mul, map_sum, ← hc]
  have step : ∀ i : Fin (2 ^ regBits N),
      c * (∑ k ∈ Finset.range r, (omega r ^ (k * j))⁻¹ * if (i : ℕ) = a ^ k % N then 1 else 0) *
        ((starRingEnd ℂ) c * ∑ k' ∈ Finset.range r,
          (starRingEnd ℂ) ((omega r ^ (k' * l))⁻¹) * (starRingEnd ℂ) (if (i : ℕ) = a ^ k' % N then 1 else 0))
      = c * (starRingEnd ℂ) c * ∑ k ∈ Finset.range r, ∑ k' ∈ Finset.range r,
          (omega r ^ (k * j))⁻¹ * (starRingEnd ℂ) ((omega r ^ (k' * l))⁻¹) *
            (if (i : ℕ) = a ^ k % N ∧ (i : ℕ) = a ^ k' % N then 1 else 0) := by
    intro i
    rw [mul_mul_mul_comm, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
    by_cases h1 : (i : ℕ) = a ^ k % N <;> by_cases h2 : (i : ℕ) = a ^ k' % N <;>
      simp only [h1, h2, if_true, if_false, and_self, and_false, false_and, map_one, map_zero,
        mul_one, mul_zero, true_and, and_true]
    all_goals (split_ifs <;> simp)
  simp_rw [step]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have inner : ∀ k ∈ Finset.range r, (∑ i : Fin (2 ^ regBits N), ∑ k' ∈ Finset.range r,
      (omega r ^ (k * j))⁻¹ * (starRingEnd ℂ) ((omega r ^ (k' * l))⁻¹) *
        (if (i : ℕ) = a ^ k % N ∧ (i : ℕ) = a ^ k' % N then (1 : ℂ) else 0))
      = (omega r ^ (k * j))⁻¹ * (starRingEnd ℂ) ((omega r ^ (k * l))⁻¹) := by
    intro k hk
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single k]
    · have hm : a ^ k % N < 2 ^ regBits N := lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hN
      rw [Finset.sum_eq_single ⟨a ^ k % N, hm⟩]
      · simp
      · intro b _ hb
        have : (b : ℕ) ≠ a ^ k % N := fun h => hb (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro k' hk' hkk
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [if_neg]; · ring
      rintro ⟨h1, h2⟩
      exact hkk (s_inj N a haN hcop k' k (Finset.mem_range.1 hk') (Finset.mem_range.1 hk) (h2 ▸ h1))
    · intro h; exact absurd hk h
  rw [Finset.sum_congr rfl inner, geom_ortho r j l hr0 hj hl, hcc]
  have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  split_ifs
  · field_simp
  · simp


lemma sq_norm_c (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma sumsq (N a : ℕ) (ha : 1 < a) (haN : a < N) (hcop : Nat.Coprime a N) (b : ℕ → ℂ) :
    ∑ i, ‖∑ j ∈ Finset.range (ord N a), b j * eigState N a (regBits N) j i‖ ^ 2
      = ∑ j ∈ Finset.range (ord N a), ‖b j‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.ofReal_pow, sq_norm_c, map_sum, map_mul]
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  have : ∀ j ∈ Finset.range (ord N a), (∑ i : Fin (2 ^ regBits N), ∑ l ∈ Finset.range (ord N a),
      b j * eigState N a (regBits N) j i * ((starRingEnd ℂ) (b l) * (starRingEnd ℂ) (eigState N a (regBits N) l i)))
      = b j * (starRingEnd ℂ) (b j) := by
    intro j hj
    rw [Finset.sum_comm]
    have e : ∀ l ∈ Finset.range (ord N a), (∑ i : Fin (2 ^ regBits N),
        b j * eigState N a (regBits N) j i * ((starRingEnd ℂ) (b l) * (starRingEnd ℂ) (eigState N a (regBits N) l i)))
        = b j * (starRingEnd ℂ) (b l) * (if j = l then 1 else 0) := by
      intro l hl
      rw [← ortho N a ha haN hcop j l (Finset.mem_range.1 hj) (Finset.mem_range.1 hl), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    rw [Finset.sum_congr rfl e]
    simp [Finset.sum_ite_eq, Finset.mem_range.1 hj]
  rw [Finset.sum_congr rfl this]

theorem measure_first (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (k : Fin (2 ^ (2 * regBits N))) :
    measureFirst (orderFindingOutput N a) k
      = (1 / (ord N a : ℝ)) * ∑ j ∈ Finset.range (ord N a),
          measureFirst (phaseEstimationCircuit N a (regBits N) (2 * regBits N) *ᵥ
            tensorState (ket (2 ^ (2 * regBits N)) 0) (eigState N a (regBits N) j)) k := by
  set r := ord N a with hr
  have hr0 : 0 < r := ShorGate.ord_pos N a haN hcop
  set c : ℂ := (1 / Real.sqrt r : ℂ) with hc
  have hcn : ‖c‖ ^ 2 = 1 / r := by
    rw [hc, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      div_pow, Real.sq_sqrt (Nat.cast_nonneg _), one_pow]
  let φ : ℕ → Fin (2 ^ (2 * regBits N)) → ℂ := fun j => qftInv (2 * regBits N) *ᵥ fun x => (1 / Real.sqrt (2 ^ (2 * regBits N)) : ℂ) * (omega r ^ j) ^ (x : ℕ)
  have hcirc : ∀ j, phaseEstimationCircuit N a (regBits N) (2 * regBits N) *ᵥ
      tensorState (ket (2 ^ (2 * regBits N)) 0) (eigState N a (regBits N) j) = tensorState (φ j) (eigState N a (regBits N) j) :=
    fun j => circuit_eig N a (regBits N) (2 * regBits N) _ _ (ShorGate.eigvec N a ha haN hcop j).2
  have hout : orderFindingOutput N a = c • ∑ j ∈ Finset.range r, tensorState (φ j) (eigState N a (regBits N) j) := by
    unfold orderFindingOutput
    rw [← ShorSumEig.ket_one N a ha haN hcop]
    have : tensorState (ket (2 ^ (2 * regBits N)) 0) ((1 / Real.sqrt (ord N a) : ℂ) • ∑ j ∈ Finset.range (ord N a), eigState N a (regBits N) j)
        = c • ∑ j ∈ Finset.range r, tensorState (ket (2 ^ (2 * regBits N)) 0) (eigState N a (regBits N) j) := by
      funext p
      simp only [tensorState, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum, ← hr, ← hc]
      refine Finset.sum_congr rfl (fun j _ => ?_); ring
    rw [this, mulVec_smul, mulVec_sum]
    simp_rw [hcirc]
  rw [hout]
  unfold measureFirst
  have lhs : ∀ i, (c • ∑ j ∈ Finset.range r, tensorState (φ j) (eigState N a (regBits N) j)) (k, i)
      = ∑ j ∈ Finset.range r, (c * φ j k) * eigState N a (regBits N) j i := by
    intro i
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, tensorState, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_); ring
  rw [Finset.sum_congr rfl (fun i _ => by rw [lhs i])]
  rw [sumsq N a ha haN hcop (fun j => c * φ j k)]
  simp_rw [hcirc]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hn1 : ∑ i, ‖eigState N a (regBits N) j i‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    push_cast
    simp only [← Complex.ofReal_pow, sq_norm_c]
    rw [ortho N a ha haN hcop j j (Finset.mem_range.1 hj) (Finset.mem_range.1 hj), if_pos rfl]
  simp only [tensorState, norm_mul, mul_pow]
  rw [← Finset.mul_sum, hn1, hcn]
  ring

end ShorPE
open ShorWiki Matrix Kronecker

namespace ShorPE

lemma ord_lt (N a : ℕ) (ha : 1 < a) (haN : a < N) (hcop : Nat.Coprime a N) : ord N a < N := by
  have : NeZero N := ⟨by omega⟩
  unfold ord
  have : orderOf (ZMod.unitOfCoprime a hcop) = orderOf (a : ZMod N) := by
    rw [← orderOf_units]; rfl
  rw [← this]
  calc _ ≤ Fintype.card (ZMod N)ˣ := orderOf_le_card_univ
    _ = Nat.totient N := ZMod.card_units_eq_totient N
    _ < N := Nat.totient_lt N (by omega)

lemma cf_part (N a : ℕ) (ha : 1 < a) (haN : a < N) (hcop : Nat.Coprime a N) (j : ℕ)
    (k : Fin (2 ^ (2 * regBits N)))
    (hk : |((k : ℕ) : ℝ) / 2 ^ (2 * regBits N) - (j : ℝ) / ord N a| ≤ 1 / 2 ^ (2 * regBits N + 1)) :
    ∃ m : ℕ,
      (Real.convergent (((k : ℕ) : ℝ) / 2 ^ (2 * regBits N)) m).num = ((j / Nat.gcd j (ord N a) : ℕ) : ℤ) ∧
      (Real.convergent (((k : ℕ) : ℝ) / 2 ^ (2 * regBits N)) m).den = ord N a / Nat.gcd j (ord N a) := by
  set r := ord N a with hr
  have hr0 : 0 < r := ShorGate.ord_pos N a haN hcop
  have hrN : r < N := ord_lt N a ha haN hcop
  have hN : N ≤ 2 ^ regBits N := Nat.le_pow_clog (by norm_num) N
  set φ : ℝ := ((k : ℕ) : ℝ) / 2 ^ (2 * regBits N)
  set g := Nat.gcd j r with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hr0
  set j' := j / g with hj'
  set r' := r / g with hr'
  have hcop' : Nat.Coprime j' r' := Nat.coprime_div_gcd_div_gcd hg0
  have hjg : j = j' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left j r)).symm
  have hrg : r = r' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right j r)).symm
  have hr'0 : 0 < r' := Nat.div_pos (Nat.gcd_le_right _ hr0) hg0
  set q : ℚ := ((j' : ℤ) : ℚ) / ((r' : ℤ) : ℚ) with hq
  have hnum : q.num = j' := by
    rw [hq, Rat.num_div_eq_of_coprime (by exact_mod_cast hr'0) (by simpa using hcop')]
  have hden : (q.den : ℤ) = r' := by
    rw [hq, Rat.den_div_eq_of_coprime (by exact_mod_cast hr'0) (by simpa using hcop')]
  have hden' : q.den = r' := by exact_mod_cast hden
  have hqR : ((q : ℚ) : ℝ) = (j : ℝ) / r := by
    rw [hq]; push_cast
    rw [hjg, hrg]; push_cast
    have : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
    field_simp
  have hr'R : (0 : ℝ) < r' := by exact_mod_cast hr'0
  have hr'N : (r' : ℝ) < N := by
    have : r' ≤ r := Nat.div_le_self r g
    exact_mod_cast (lt_of_le_of_lt this hrN)
  have hNM : (N : ℝ) ^ 2 ≤ 2 ^ (2 * regBits N) := by
    have : (N : ℝ) ≤ 2 ^ regBits N := by exact_mod_cast hN
    rw [mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) this 2
  have hlt : |φ - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2) := by
    rw [hqR, hden']
    refine lt_of_le_of_lt hk ?_
    rw [pow_succ]
    apply one_div_lt_one_div_of_lt (by positivity)
    have : (r' : ℝ) ^ 2 < (N : ℝ) ^ 2 := pow_lt_pow_left₀ hr'N hr'R.le (by norm_num)
    nlinarith
  obtain ⟨m, hm⟩ := Real.exists_rat_eq_convergent hlt
  refine ⟨m, ?_, ?_⟩
  · rw [← hm, hnum]
  · rw [← hm, hden']

lemma exists_close (N a : ℕ) (ha : 1 < a) (haN : a < N) (hcop : Nat.Coprime a N) (j : ℕ) (hj : j < ord N a) :
    ∃ k : Fin (2 ^ (2 * regBits N)),
      |((k : ℕ) : ℝ) / 2 ^ (2 * regBits N) - (j : ℝ) / ord N a| ≤ 1 / 2 ^ (2 * regBits N + 1) := by
  set r := ord N a with hr
  have hr0 : 0 < r := ShorGate.ord_pos N a haN hcop
  have hrN : r < N := ord_lt N a ha haN hcop
  have hN : N ≤ 2 ^ regBits N := Nat.le_pow_clog (by norm_num) N
  set M : ℝ := 2 ^ (2 * regBits N) with hM
  have hMpos : 0 < M := by positivity
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hrM : (r : ℝ) < M := by
    have h1 : (r : ℝ) < N := by exact_mod_cast hrN
    have h2 : (N : ℝ) ≤ 2 ^ regBits N := by exact_mod_cast hN
    have h3 : (2 : ℝ) ^ regBits N ≤ M := by
      rw [hM]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  set y : ℝ := M * j / r + 1 / 2 with hy
  have hy0 : 0 ≤ y := by positivity
  set k0 := ⌊y⌋₊ with hk0
  have hfl := Nat.floor_le hy0
  have hlt := Nat.lt_floor_add_one y
  have hjr : (j : ℝ) ≤ r - 1 := by
    have : j + 1 ≤ r := hj
    have : (j : ℝ) + 1 ≤ r := by exact_mod_cast this
    linarith
  have hkM : (k0 : ℝ) < M := by
    have : M * j / r ≤ M * (r - 1) / r := by gcongr
    have e : M * (r - 1) / r = M - M / r := by field_simp
    have : M / r > 1 := by rw [gt_iff_lt, one_lt_div hrR]; exact hrM
    linarith
  have hkM' : k0 < 2 ^ (2 * regBits N) := by
    have : (k0 : ℝ) < ((2 ^ (2 * regBits N) : ℕ) : ℝ) := by push_cast; exact hkM
    exact_mod_cast this
  refine ⟨⟨k0, hkM'⟩, ?_⟩
  simp only
  rw [pow_succ, ← hM]
  rw [abs_le]
  constructor
  · have : (k0 : ℝ) > y - 1 := by linarith
    rw [hy] at this
    have e : (k0 : ℝ) / M - j / r = ((k0 : ℝ) - M * j / r) / M := by field_simp
    rw [e, le_div_iff₀ hMpos]
    have : -(1 / (M * 2)) * M = -(1 / 2) := by field_simp
    linarith
  · have e : (k0 : ℝ) / M - j / r = ((k0 : ℝ) - M * j / r) / M := by field_simp
    rw [e, div_le_iff₀ hMpos]
    have : 1 / (M * 2) * M = 1 / 2 := by field_simp
    rw [hy] at hfl
    linarith

theorem goal (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (j : ℕ) (hj : j < ord N a) :
    4 / (Real.pi ^ 2 * ord N a) ≤
        (∑ k ∈ Finset.univ.filter (fun k : Fin (2 ^ (2 * regBits N)) =>
            |((k : ℕ) : ℝ) / 2 ^ (2 * regBits N) - (j : ℝ) / ord N a|
              ≤ 1 / 2 ^ (2 * regBits N + 1)),
          measureFirst (orderFindingOutput N a) k) ∧
      ∀ k : Fin (2 ^ (2 * regBits N)),
        |((k : ℕ) : ℝ) / 2 ^ (2 * regBits N) - (j : ℝ) / ord N a|
            ≤ 1 / 2 ^ (2 * regBits N + 1) →
          ∃ m : ℕ,
            (Real.convergent (((k : ℕ) : ℝ) / 2 ^ (2 * regBits N)) m).num
                = ((j / Nat.gcd j (ord N a) : ℕ) : ℤ) ∧
            (Real.convergent (((k : ℕ) : ℝ) / 2 ^ (2 * regBits N)) m).den
                = ord N a / Nat.gcd j (ord N a) := by
  refine ⟨?_, fun k hk => cf_part N a ha haN hcop j k hk⟩
  have hr0 : 0 < ord N a := ShorGate.ord_pos N a haN hcop
  have hrR : (0 : ℝ) < ord N a := by exact_mod_cast hr0
  obtain ⟨k0, hk0⟩ := exists_close N a ha haN hcop j hj
  have hmem : k0 ∈ Finset.univ.filter (fun k : Fin (2 ^ (2 * regBits N)) =>
      |((k : ℕ) : ℝ) / 2 ^ (2 * regBits N) - (j : ℝ) / ord N a| ≤ 1 / 2 ^ (2 * regBits N + 1)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hk0
  have hnn : ∀ k ∈ Finset.univ.filter (fun k : Fin (2 ^ (2 * regBits N)) =>
      |((k : ℕ) : ℝ) / 2 ^ (2 * regBits N) - (j : ℝ) / ord N a| ≤ 1 / 2 ^ (2 * regBits N + 1)),
      0 ≤ measureFirst (orderFindingOutput N a) k := by
    intro k _; unfold measureFirst; positivity
  refine le_trans ?_ (Finset.single_le_sum hnn hmem)
  rw [measure_first N a ha haN hcop k0]
  obtain ⟨φ, hφ, hb⟩ := phase_est N a ha haN hcop j hj
  have hterm : 4 / Real.pi ^ 2 ≤ measureFirst (phaseEstimationCircuit N a (regBits N) (2 * regBits N) *ᵥ
      tensorState (ket (2 ^ (2 * regBits N)) 0) (eigState N a (regBits N) j)) k0 := by
    rw [hφ]
    have hn1 : ∑ i, ‖eigState N a (regBits N) j i‖ ^ 2 = 1 := by
      apply Complex.ofReal_injective
      push_cast
      simp only [← Complex.ofReal_pow, sq_norm_c]
      rw [ortho N a ha haN hcop j j hj hj, if_pos rfl]
    unfold measureFirst
    simp only [tensorState, norm_mul, mul_pow]
    rw [← Finset.mul_sum, hn1, mul_one]
    exact hb k0 hk0
  have hsum : measureFirst (phaseEstimationCircuit N a (regBits N) (2 * regBits N) *ᵥ
      tensorState (ket (2 ^ (2 * regBits N)) 0) (eigState N a (regBits N) j)) k0 ≤
      ∑ j' ∈ Finset.range (ord N a), measureFirst (phaseEstimationCircuit N a (regBits N) (2 * regBits N) *ᵥ
        tensorState (ket (2 ^ (2 * regBits N)) 0) (eigState N a (regBits N) j')) k0 := by
    refine Finset.single_le_sum (f := fun j' => measureFirst (phaseEstimationCircuit N a (regBits N) (2 * regBits N) *ᵥ
        tensorState (ket (2 ^ (2 * regBits N)) 0) (eigState N a (regBits N) j')) k0) (fun j' _ => ?_)
      (Finset.mem_range.2 hj)
    unfold measureFirst; positivity
  rw [show 4 / (Real.pi ^ 2 * (ord N a : ℝ)) = 1 / (ord N a : ℝ) * (4 / Real.pi ^ 2) by field_simp]
  gcongr
  linarith

end ShorPE

open ShorWiki Matrix Kronecker in
theorem solution (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (j : ℕ) (hj : j < ord N a) :
    4 / (Real.pi ^ 2 * ord N a) ≤
        (∑ k ∈ Finset.univ.filter (fun k : Fin (2 ^ (2 * regBits N)) =>
            |((k : ℕ) : ℝ) / 2 ^ (2 * regBits N) - (j : ℝ) / ord N a|
              ≤ 1 / 2 ^ (2 * regBits N + 1)),
          measureFirst (orderFindingOutput N a) k) ∧
      ∀ k : Fin (2 ^ (2 * regBits N)),
        |((k : ℕ) : ℝ) / 2 ^ (2 * regBits N) - (j : ℝ) / ord N a|
            ≤ 1 / 2 ^ (2 * regBits N + 1) →
          ∃ m : ℕ,
            (Real.convergent (((k : ℕ) : ℝ) / 2 ^ (2 * regBits N)) m).num
                = ((j / Nat.gcd j (ord N a) : ℕ) : ℤ) ∧
            (Real.convergent (((k : ℕ) : ℝ) / 2 ^ (2 * regBits N)) m).den
                = ord N a / Nat.gcd j (ord N a) :=
  ShorPE.goal N a ha haN hcop j hj
