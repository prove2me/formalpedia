-- Prove2me | solution 1 for WeightedHilbert_nonuniform_large_sieve_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T17:40:40.84022+00:00
-- url     : https://prove2.me/submissions/8179bb54-4393-4c46-910f-797a7546eaa2

import Theorems.Thm_WeightedHilbert_circle_cosecant_bound_sixteen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped BigOperators ComplexConjugate

namespace WeightedFourier

noncomputable def phase (t : ℝ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * (t : ℂ) * Complex.I)

lemma phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  unfold phase
  rw [show (Real.pi : ℂ) * ((x+y : ℝ) : ℂ) * Complex.I =
    (Real.pi : ℂ) * x * Complex.I + (Real.pi : ℂ) * y * Complex.I by push_cast; ring]
  exact Complex.exp_add _ _

lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp]

lemma conj_phase (x : ℝ) : conj (phase x) = phase (-x) := by
  simp [phase, ← Complex.exp_conj, mul_assoc]

lemma phase_sub (x y : ℝ) : phase (x-y) = phase x * conj (phase y) := by
  rw [sub_eq_add_neg, phase_add, conj_phase]

lemma sine_phase (x : ℝ) :
    2 * Complex.I * Complex.sin ((Real.pi : ℂ) * (x : ℂ)) = phase x - phase (-x) := by
  have h := Complex.two_sin (x := (Real.pi : ℂ) * (x : ℂ))
  have h' := congrArg (fun z : ℂ => Complex.I * z) h
  have he : phase (-x) = Complex.exp (-((Real.pi : ℂ) * (x : ℂ)) * Complex.I) := by
    unfold phase
    congr 1
    push_cast
    ring
  rw [he]
  unfold phase
  calc
    2 * Complex.I * Complex.sin ((Real.pi : ℂ) * (x : ℂ)) =
        Complex.I * (2 * Complex.sin ((Real.pi : ℂ) * (x : ℂ))) := by ring
    _ = _ := by rw [h']; ring_nf; simp [Complex.I_sq]

lemma geometric_phase (N : ℕ) (x : ℝ)
    (hs : Complex.sin ((Real.pi : ℂ) * (x : ℂ)) ≠ 0) :
    (∑ n ∈ Finset.range N, phase (2 * (n : ℝ) * x)) =
      (phase ((2*(N : ℝ)-1)*x) - phase (-x)) /
        (2 * Complex.I * Complex.sin ((Real.pi : ℂ) * (x : ℂ))) := by
  apply (eq_div_iff (mul_ne_zero (by simp) hs)).mpr
  rw [Finset.sum_mul]
  have hstep (n : ℕ) : phase (2 * (n : ℝ) * x) *
      (2 * Complex.I * Complex.sin ((Real.pi : ℂ) * (x : ℂ))) =
      phase ((2*((n+1 : ℕ) : ℝ)-1)*x) - phase ((2*(n : ℝ)-1)*x) := by
    rw [sine_phase, mul_sub, ← phase_add, ← phase_add]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  simp_rw [hstep]
  simpa using Finset.sum_range_sub (fun n : ℕ => phase ((2*(n : ℝ)-1)*x)) N

lemma gram_pointwise {ι : Type} [Fintype ι] (θ : ι → ℝ) (v : ι → ℂ) (n : ℕ) :
    (‖∑ r, v r * phase (2*(n : ℝ)*θ r)‖ : ℂ)^2 =
      ∑ r, ∑ s, v r * conj (v s) * phase (2*(n : ℝ)*(θ r-θ s)) := by
  rw [← Complex.mul_conj']
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [show 2*(n : ℝ)*(θ r-θ s) = 2*(n : ℝ)*θ r-2*(n : ℝ)*θ s by ring,
    phase_sub]
  ring

lemma gram_sum {ι : Type} [Fintype ι] (N : ℕ) (θ : ι → ℝ) (v : ι → ℂ) :
    ((∑ n ∈ Finset.range N, ‖∑ r, v r * phase (2*(n : ℝ)*θ r)‖^2 : ℝ) : ℂ) =
      ∑ r, ∑ s, v r * conj (v s) *
        ∑ n ∈ Finset.range N, phase (2*(n : ℝ)*(θ r-θ s)) := by
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, gram_pointwise]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

noncomputable def hilbert {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ : ι → ℝ) (v : ι → ℂ) : ℂ :=
  ∑ r, ∑ s, if r = s then 0 else
    v r * conj (v s) / Complex.sin ((Real.pi : ℂ) * ((θ r-θ s : ℝ) : ℂ))

lemma modulated_pair {ι : Type} (θ : ι → ℝ) (v : ι → ℂ) (t : ℝ) (r s : ι) :
    (v r * phase (t*θ r)) * conj (v s * phase (t*θ s)) =
      v r * conj (v s) * phase (t*(θ r-θ s)) := by
  rw [map_mul, show t*(θ r-θ s) = t*θ r-t*θ s by ring, phase_sub]
  ring

lemma offdiag_identity {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (θ : ι → ℝ) (v : ι → ℂ)
    (hs : ∀ r s, r ≠ s → Complex.sin ((Real.pi : ℂ) * ((θ r-θ s : ℝ) : ℂ)) ≠ 0) :
    (∑ r, ∑ s, if r = s then (0 : ℂ) else v r * conj (v s) *
      ∑ n ∈ Finset.range N, phase (2*(n : ℝ)*(θ r-θ s))) =
      (hilbert θ (fun r => v r * phase ((2*(N : ℝ)-1)*θ r)) -
        hilbert θ (fun r => v r * phase (-θ r))) / (2*Complex.I) := by
  unfold hilbert
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hmem
  by_cases hrs : r = s
  · simp [hrs]
  · simp only [hrs, ↓reduceIte]
    have hn (r : ι) : phase (-θ r) = phase ((-1)*θ r) := by congr 1; ring
    simp_rw [hn, modulated_pair]
    rw [geometric_phase N (θ r-θ s) (hs r s hrs)]
    have he : phase ((-1)*(θ r-θ s)) = phase (-(θ r-θ s)) := by congr 1; ring
    rw [he]
    field_simp
    <;> ring

lemma offdiag_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (θ δ : ι → ℝ) (v : ι → ℂ) (C : ℝ)
    (hs : ∀ r s, r ≠ s → Complex.sin ((Real.pi : ℂ) * ((θ r-θ s : ℝ) : ℂ)) ≠ 0)
    (hH : ∀ w : ι → ℂ, ‖hilbert θ w‖ ≤ C * ∑ r, ‖w r‖^2 / δ r) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else v r * conj (v s) *
      ∑ n ∈ Finset.range N, phase (2*(n : ℝ)*(θ r-θ s))‖ ≤
        C * ∑ r, ‖v r‖^2 / δ r := by
  rw [offdiag_identity N θ v hs, norm_div]
  have ha := hH (fun r => v r * phase ((2*(N : ℝ)-1)*θ r))
  have hb := hH (fun r => v r * phase (-θ r))
  simp only [norm_mul, norm_phase, mul_one] at ha hb
  have ht := norm_sub_le
    (hilbert θ (fun r => v r * phase ((2*(N : ℝ)-1)*θ r)))
    (hilbert θ (fun r => v r * phase (-θ r)))
  norm_num [norm_mul, Complex.norm_I]
  linarith

lemma dual_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (θ δ : ι → ℝ) (v : ι → ℂ) (C : ℝ)
    (hs : ∀ r s, r ≠ s → Complex.sin ((Real.pi : ℂ) * ((θ r-θ s : ℝ) : ℂ)) ≠ 0)
    (hH : ∀ w : ι → ℂ, ‖hilbert θ w‖ ≤ C * ∑ r, ‖w r‖^2 / δ r) :
    (∑ n ∈ Finset.range N, ‖∑ r, v r * phase (2*(n : ℝ)*θ r)‖^2) ≤
      ∑ r, ((N : ℝ) + C / δ r) * ‖v r‖^2 := by
  let K (r s : ι) : ℂ := v r * conj (v s) *
    ∑ n ∈ Finset.range N, phase (2*(n : ℝ)*(θ r-θ s))
  have hd (r : ι) : K r r = (N : ℂ) * (‖v r‖ : ℂ)^2 := by
    simp only [K, sub_self, mul_zero, zero_mul, phase, Complex.ofReal_zero, Complex.exp_zero,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Complex.mul_conj']
    ring
  have hsplit (r s : ι) : K r s =
      (if r = s then (N : ℂ) * (‖v r‖ : ℂ)^2 else 0) +
        (if r = s then 0 else K r s) := by
    by_cases h : r = s
    · subst s; simp [hd]
    · simp [h]
  have he : ((∑ n ∈ Finset.range N, ‖∑ r, v r * phase (2*(n : ℝ)*θ r)‖^2 : ℝ) : ℂ) =
      ((N : ℝ) * ∑ r, ‖v r‖^2 : ℝ) +
      ∑ r, ∑ s, if r = s then (0 : ℂ) else K r s := by
    rw [gram_sum]
    change (∑ r, ∑ s, K r s) = _
    have he' : (∑ r, ∑ s, K r s) = ∑ r, ∑ s,
        ((if r = s then (N : ℂ) * (‖v r‖ : ℂ)^2 else 0) +
          (if r = s then 0 else K r s)) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hmem
      exact hsplit r s
    rw [he']
    simp only [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    push_cast
    rw [Finset.mul_sum]
  have ho := offdiag_bound N θ δ v C hs hH
  change ‖∑ r, ∑ s, if r = s then (0 : ℂ) else K r s‖ ≤ _ at ho
  have hm : 0 ≤ ∑ r, ‖v r‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : 0 ≤ ∑ n ∈ Finset.range N, ‖∑ r, v r * phase (2*(n : ℝ)*θ r)‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ht := norm_add_le (((N : ℝ) * ∑ r, ‖v r‖^2 : ℝ) : ℂ)
    (∑ r, ∑ s, if r = s then (0 : ℂ) else K r s)
  rw [← he] at ht
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N) hm)] at ht
  calc
    _ ≤ (N : ℝ) * ∑ r, ‖v r‖^2 + C * ∑ r, ‖v r‖^2 / δ r :=
      ht.trans (add_le_add le_rfl ho)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      ring

lemma weighted_primal_of_dual {ι : Type} [Fintype ι]
    (N : ℕ) (M : ι → ℕ → ℂ) (w : ι → ℝ) (hw : ∀ r, 0 < w r)
    (hdual : ∀ v : ι → ℂ,
      (∑ n ∈ Finset.range N, ‖∑ r, v r * M r n‖^2) ≤ ∑ r, w r * ‖v r‖^2)
    (a : ℕ → ℂ) :
    (∑ r, ‖∑ n ∈ Finset.range N, a n * M r n‖^2 / w r) ≤
      ∑ n ∈ Finset.range N, ‖a n‖^2 := by
  classical
  let S (r : ι) : ℂ := ∑ n ∈ Finset.range N, a n * M r n
  let v (r : ι) : ℂ := conj (S r) / (w r : ℂ)
  let b (n : ℕ) : ℂ := ∑ r, v r * M r n
  let Q : ℝ := ∑ r, ‖S r‖^2 / w r
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun r _ => div_nonneg (sq_nonneg _) (hw r).le)
  have hmass : (∑ r, w r * ‖v r‖^2) = Q := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [v, norm_div, RCLike.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hw r)]
    field_simp
  have he : (∑ n ∈ Finset.range N, a n * b n) = (Q : ℂ) := by
    dsimp only [b]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    dsimp only [Q]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hfactor : (∑ n ∈ Finset.range N, a n * (v r * M r n)) = S r * v r := by
      dsimp only [S]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [hfactor]
    dsimp only [v]
    rw [← mul_div_assoc, Complex.mul_conj']
    push_cast
    rfl
  have hb := hdual v
  rw [hmass] at hb
  change (∑ n ∈ Finset.range N, ‖b n‖^2) ≤ Q at hb
  have hnorm : ‖∑ n ∈ Finset.range N, a n * b n‖ ≤
      ∑ n ∈ Finset.range N, ‖a n‖ * ‖b n‖ := by
    simpa only [norm_mul] using norm_sum_le (Finset.range N) (fun n => a n * b n)
  rw [he] at hnorm
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQ] at hnorm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun n => ‖a n‖) (fun n => ‖b n‖)
  have hA : 0 ≤ ∑ n ∈ Finset.range N, ‖a n‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hprod := mul_le_mul_of_nonneg_left hb hA
  have hsq : Q^2 ≤ (∑ n ∈ Finset.range N, ‖a n‖ * ‖b n‖)^2 :=
    pow_le_pow_left₀ hQ hnorm 2
  change Q ≤ _
  nlinarith

lemma primal_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (θ δ : ι → ℝ) (C : ℝ) (hC : 0 < C) (hδ : ∀ r, 0 < δ r)
    (hs : ∀ r s, r ≠ s → Complex.sin ((Real.pi : ℂ) * ((θ r-θ s : ℝ) : ℂ)) ≠ 0)
    (hH : ∀ w : ι → ℂ, ‖hilbert θ w‖ ≤ C * ∑ r, ‖w r‖^2 / δ r)
    (a : ℕ → ℂ) :
    (∑ r, ‖∑ n ∈ Finset.range N, a n * phase (2*(n : ℝ)*θ r)‖^2 /
      ((N : ℝ) + C / δ r)) ≤ ∑ n ∈ Finset.range N, ‖a n‖^2 := by
  apply weighted_primal_of_dual N (fun r n => phase (2*(n : ℝ)*θ r))
    (fun r => (N : ℝ) + C / δ r) _ _ a
  · intro r
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) (div_pos hC (hδ r))
  · intro v
    exact dual_bound N θ δ v C hs hH

lemma sine_nonzero_of_gap (x d : ℝ) (hd : 0 < d)
    (hgap : ∀ m : ℤ, d ≤ |x + m|) :
    Complex.sin ((Real.pi : ℂ) * (x : ℂ)) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]
  intro k hk
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hx : (x : ℂ) = (k : ℂ) := by
    apply mul_left_cancel₀ hp
    calc
      (Real.pi : ℂ) * (x : ℂ) = (k : ℂ) * (Real.pi : ℂ) := hk
      _ = _ := mul_comm _ _
  have hx' : x = (k : ℝ) := by exact_mod_cast hx
  have h := hgap (-k)
  simp only [hx', Int.cast_neg, add_neg_cancel, abs_zero] at h
  exact (not_le_of_gt hd) h

theorem nonuniform_from_circle {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (θ δ : ι → ℝ) (a : ℕ → ℂ)
    (hpos : ∀ r, 0 < δ r)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r-θ s+m|)
    (hH : ∀ v : ι → ℂ,
      ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
        v r * conj (v s) / Complex.sin ((Real.pi : ℂ) * ((θ r-θ s : ℝ) : ℂ))‖ ≤
          16 * ∑ r, ‖v r‖^2 / δ r) :
    (∑ r, ‖∑ n ∈ Finset.range N,
      a n * Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(θ r : ℂ))‖^2 /
      ((N : ℝ)+16/δ r)) ≤ ∑ n ∈ Finset.range N, ‖a n‖^2 := by
  have h := primal_bound N θ δ 16 (by norm_num) hpos
    (fun r s hrs => sine_nonzero_of_gap _ _ (hpos r) (hgap r s hrs)) hH a
  have he (n : ℕ) (r : ι) : phase (2*(n : ℝ)*θ r) =
      Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(θ r : ℂ)) := by
    unfold phase
    congr 1
    push_cast
    ring
  simpa only [he] using h

end WeightedFourier

theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (θ δ : ι → ℝ) (a : ℕ → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r-θ s+m|) :
    (∑ r, ‖∑ n ∈ Finset.range N,
      a n * Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(θ r : ℂ))‖^2 /
      ((N : ℝ)+16/δ r)) ≤ ∑ n ∈ Finset.range N, ‖a n‖^2 := by
  exact WeightedFourier.nonuniform_from_circle N θ δ a hpos hgap
    (fun v => WeightedHilbert_circle_cosecant_bound_sixteen θ δ v hpos hunit hgap)
#print axioms solution
