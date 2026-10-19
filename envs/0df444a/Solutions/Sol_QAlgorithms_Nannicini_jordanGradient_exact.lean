-- Prove2me | solution 1 for QAlgorithms.Nannicini.jordanGradient_exact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T03:45:34.226241+00:00
-- url     : https://prove2.me/submissions/5528a290-8078-495c-b455-284cb674831d

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05a_Model
set_option autoImplicit false
open QAlgorithms
open scoped ComplexConjugate

private noncomputable def phase (q k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / ((2 : ℝ) ^ q : ℂ))

private lemma phase_add (q a b : ℕ) : phase q (a + b) = phase q a * phase q b := by
  simp only [phase, Nat.cast_add, mul_add, add_div, Complex.exp_add]

private lemma phase_mod (q k : ℕ) : phase q (k % 2 ^ q) = phase q k := by
  have hp (t : ℕ) : phase q (2 ^ q * t) = 1 := by
    unfold phase
    have he : 2 * (Real.pi : ℂ) * Complex.I * ((2 ^ q * t : ℕ) : ℂ) /
        ((2 : ℝ) ^ q : ℂ) = (t : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    rw [he, Complex.exp_nat_mul]
    simp [Complex.exp_two_pi_mul_I]
  have h := congrArg (phase q) (Nat.mod_add_div k (2 ^ q))
  simpa only [phase_add, hp, mul_one] using h

private lemma phase_norm (q k : ℕ) : ‖phase q k‖ = 1 := by
  unfold phase
  have he : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / ((2 : ℝ) ^ q : ℂ) =
      ((2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ q : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.norm_exp, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    mul_zero, zero_mul, sub_self, Real.exp_zero]

private lemma phase_conj_mul (q k : ℕ) : conj (phase q k) * phase q k = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, phase_norm]
  norm_num

private lemma bits_natToBits (q k : ℕ) : bitsToNat (natToBits q k) = k % 2 ^ q := by
  rw [← bitsEquivFin_apply]
  simp [natToBits]

private lemma shift_bij (q k : ℕ) : Function.Bijective
    (fun y : Qubits q => natToBits q (bitsToNat y + k)) := by
  apply (Finite.injective_iff_bijective).mp
  intro a b h
  have hm := congrArg bitsToNat h
  simp only [bits_natToBits] at hm
  have ha : bitsToNat a < 2 ^ q := by simpa only [bitsEquivFin_apply] using (bitsEquivFin q a).isLt
  have hb : bitsToNat b < 2 ^ q := by simpa only [bitsEquivFin_apply] using (bitsEquivFin q b).isLt
  have he : bitsToNat a = bitsToNat b := Nat.ModEq.add_right_cancel' k hm |>.eq_of_lt_of_lt ha hb
  apply (bitsEquivFin q).injective
  apply Fin.ext
  simpa only [bitsEquivFin_apply] using he

private lemma oracle_apply (d q : ℕ) (F : (Fin d → Qubits q) → ℕ)
    (v : EuclideanSpace ℂ ((Fin d → Qubits q) × Qubits q))
    (x : Fin d → Qubits q) (y : Qubits q) :
    act (modAddOracle d q F) v (x, natToBits q (bitsToNat y + F x)) = v (x,y) := by
  classical
  simp only [act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    modAddOracle, Matrix.of_apply]
  have hi := (shift_bij q (F x)).injective
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single x]
  · simp only [true_and]
    have hh (z : Qubits q) :
        (natToBits q (bitsToNat y + F x) = natToBits q (bitsToNat z + F x)) ↔ z = y := by
      constructor
      · intro h; exact (hi h).symm
      · rintro rfl; rfl
    simp only [hh]
    simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

private lemma act_ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) : act A (ket i) j = A j i := by
  classical
  simp [act, ket, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]

private lemma alltrue_value (q : ℕ) : bitsToNat (fun _ : Fin q => true) = 2 ^ q - 1 := by
  change (∑ i : Fin q, (2 : ℕ) ^ (q - 1 - (i : ℕ))) = _
  calc
    _ = ∑ i ∈ Finset.range q, (2 : ℕ) ^ (q - 1 - i) := Fin.sum_univ_eq_sum_range _ _
    _ = _ := by rw [Finset.sum_range_reflect]; simpa using Nat.geomSum_eq (m := 2) (by decide) q

private lemma qft_true (q : ℕ) (y : Qubits q) :
    act (qftQubits q) (ket fun _ => true) y =
      conj (phase q (bitsToNat y)) / (Real.sqrt (2 ^ q : ℕ) : ℂ) := by
  rw [act_ket]
  simp only [qftQubits, Matrix.submatrix_apply, qftMatrix, Matrix.of_apply,
    bitsEquivFin_apply, alltrue_value]
  congr 1
  unfold phase
  rw [← Complex.exp_conj]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨bitsToNat y, ?_⟩
  have hN : ((2 ^ q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.two_pow_pos q))
  have hc : (((2 ^ q - 1 : ℕ) : ℂ)) = ((2 ^ q : ℕ) : ℂ) - 1 := by
    rw [Nat.cast_sub (by have := Nat.two_pow_pos q; omega)]
    simp
  simp only [hc, map_div₀, map_mul, map_pow, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast, map_natCast, map_intCast]
  norm_num
  field_simp
  ring

private lemma hadamard_zero (d q : ℕ) (x : Fin d → Qubits q) :
    act (piKron d (hadamardN q)) (ket fun _ _ => false) x =
      ((Real.sqrt (2 ^ q : ℕ))⁻¹ : ℂ) ^ d := by
  rw [act_ket]
  have hgen : ∀ t : ℕ, Real.sqrt ((2 : ℝ) ^ t) = Real.sqrt 2 ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ q ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  have hz (u : Qubits q) : dotBits (fun _ => false) u = false := by
    simp only [dotBits, Bool.false_and]
    exact Finset.sum_const_zero
  simp [piKron, hadamardN, hz, hgen, inv_pow]

private lemma kickback (d q : ℕ) (F : (Fin d → Qubits q) → ℕ)
    (x : Fin d → Qubits q) (z : Qubits q) :
    act (modAddOracle d q F)
      (tensorVec (act (piKron d (hadamardN q)) (ket fun _ _ => false))
        (act (qftQubits q) (ket fun _ => true))) (x,z) =
      ((Real.sqrt (2 ^ q : ℕ))⁻¹ : ℂ) ^ d * phase q (F x) *
        (conj (phase q (bitsToNat z)) / (Real.sqrt (2 ^ q : ℕ) : ℂ)) := by
  obtain ⟨y, rfl⟩ := (shift_bij q (F x)).surjective z
  rw [oracle_apply]
  simp only [tensorVec, hadamard_zero, qft_true, bits_natToBits, phase_mod, phase_add, map_mul]
  have h := phase_conj_mul q (F x)
  calc
    _ = ((Real.sqrt (2 ^ q : ℕ))⁻¹ : ℂ) ^ d *
        (conj (phase q (bitsToNat y)) * (conj (phase q (F x)) * phase q (F x))) /
          (Real.sqrt (2 ^ q : ℕ) : ℂ) := by rw [h]; ring
    _ = _ := by ring

private lemma phase_linear (d q : ℕ) (g x : Fin d → Qubits q) (b : ℕ) :
    phase q (∑ i, bitsToNat (g i) * bitsToNat (x i) + b) =
      (∏ i, phase q (bitsToNat (g i) * bitsToNat (x i))) * phase q b := by
  rw [phase_add]
  congr 1
  simp only [phase, Nat.cast_sum, Finset.mul_sum, Finset.sum_div, Complex.exp_sum]

private lemma inverse_qft_entry (q : ℕ) (a x : Qubits q) :
    star (qftQubits q) a x =
      conj (phase q (bitsToNat a * bitsToNat x)) / (Real.sqrt (2 ^ q : ℕ) : ℂ) := by
  change conj (qftQubits q x a) = _
  simp only [qftQubits, Matrix.submatrix_apply, qftMatrix,
    Matrix.of_apply, bitsEquivFin_apply, phase]
  rw [map_div₀, Complex.conj_ofReal]
  congr 2
  push_cast
  ring

private lemma register_cancellation (d q : ℕ) (g x : Fin d → Qubits q) :
    piKron d (star (qftQubits q)) g x *
      phase q (∑ i, bitsToNat (g i) * bitsToNat (x i)) =
        ((Real.sqrt (2 ^ q : ℕ))⁻¹ : ℂ) ^ d := by
  have hlin := phase_linear d q g x 0
  have hz : phase q 0 = 1 := by simp [phase]
  simp only [add_zero, hz, mul_one] at hlin
  rw [hlin]
  simp only [piKron, Matrix.of_apply, inverse_qft_entry, ← Finset.prod_mul_distrib]
  have hh (i : Fin d) :
      conj (phase q (bitsToNat (g i) * bitsToNat (x i))) /
        (Real.sqrt (2 ^ q : ℕ) : ℂ) * phase q (bitsToNat (g i) * bitsToNat (x i)) =
        ((Real.sqrt (2 ^ q : ℕ))⁻¹ : ℂ) := by
    rw [div_mul_eq_mul_div, phase_conj_mul, one_div]
  simp only [hh, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private lemma act_kron_one {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ (ι × κ)) (x : ι) (z : κ) :
    act (Matrix.kronecker A (1 : Matrix κ κ ℂ)) v (x,z) = ∑ y, A x y * v (y,z) := by
  classical
  change (∑ w : ι × κ, Matrix.kronecker A (1 : Matrix κ κ ℂ) (x,z) w * v w) = _
  rw [Fintype.sum_prod_type]
  simp [Matrix.kronecker_apply, Matrix.one_apply, mul_ite, ite_mul]

private lemma jordan_coordinate (d q : ℕ) (g : Fin d → Qubits q) (b : ℕ) (z : Qubits q) :
    jordanGradientState d q
      (fun x => ∑ i, bitsToNat (g i) * bitsToNat (x i) + b) (g,z) =
      phase q b * conj (phase q (bitsToNat z)) / (Real.sqrt (2 ^ q : ℕ) : ℂ) := by
  classical
  let s : ℂ := (Real.sqrt (2 ^ q : ℕ) : ℂ)
  have hs : s ^ 2 = (2 ^ q : ℕ) := by
    dsimp [s]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_cast
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < (2 ^ q : ℕ))))
  unfold jordanGradientState
  rw [act_kron_one]
  simp only [kickback, phase_add]
  have hc (x : Fin d → Qubits q) :
      piKron d (star (qftQubits q)) g x *
        (s⁻¹ ^ d * (phase q (∑ i, bitsToNat (g i) * bitsToNat (x i)) * phase q b) *
          (conj (phase q (bitsToNat z)) / s)) =
        s⁻¹ ^ (2*d) * phase q b * conj (phase q (bitsToNat z)) / s := by
    calc
      _ = (piKron d (star (qftQubits q)) g x *
          phase q (∑ i, bitsToNat (g i) * bitsToNat (x i))) *
          s⁻¹ ^ d * phase q b * conj (phase q (bitsToNat z)) / s := by ring
      _ = _ := by rw [register_cancellation]; dsimp [s]; ring
  change (∑ x : Fin d → Qubits q,
    piKron d (star (qftQubits q)) g x *
      (s⁻¹ ^ d * (phase q (∑ i, bitsToNat (g i) * bitsToNat (x i)) * phase q b) *
        (conj (phase q (bitsToNat z)) / s))) = _
  simp only [hc]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
  have hcard : Fintype.card (Qubits q) = 2 ^ q := by simp [Qubits]
  rw [hcard]
  simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  have hcancel : ((2 ^ q : ℕ) : ℂ) ^ d * s⁻¹ ^ (2*d) = 1 := by
    rw [← hs, pow_mul, inv_pow, ← mul_pow]
    simp [hs0]
  calc
    _ = (((2 ^ q : ℕ) : ℂ) ^ d * s⁻¹ ^ (2*d)) *
        phase q b * conj (phase q (bitsToNat z)) / s := by
      dsimp [s]
      push_cast
      ring
    _ = _ := by rw [hcancel]; simp [s]

theorem solution (d q : ℕ) (g : Fin d → Qubits q) (b : ℕ) :
    let F : (Fin d → Qubits q) → ℕ := fun x => ∑ i, bitsToNat (g i) * bitsToNat (x i) + b
    marginalFst (jordanGradientState d q F) g = 1 := by
  classical
  dsimp only
  unfold marginalFst
  have hp (z : Qubits q) :
      prob (jordanGradientState d q
        (fun x => ∑ i, bitsToNat (g i) * bitsToNat (x i) + b)) (g,z) =
        ((2 ^ q : ℕ) : ℝ)⁻¹ := by
    simp only [prob, ket, EuclideanSpace.inner_single_left, one_mul, jordan_coordinate,
      norm_div, norm_mul, phase_norm, Complex.norm_conj, map_one, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), one_mul, div_pow, one_pow,
      Real.sq_sqrt (by positivity : (0:ℝ) ≤ (2 ^ q : ℕ)), one_div]
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  simp_rw [hp]
  rw [Finset.sum_const, Finset.card_univ]
  have hc : Fintype.card (Qubits q) = 2 ^ q := by simp [Qubits]
  rw [hc, nsmul_eq_mul, mul_inv_cancel₀ (by positivity)]
