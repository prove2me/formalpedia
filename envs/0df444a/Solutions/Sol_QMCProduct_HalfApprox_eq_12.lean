-- Prove2me | solution 1 for QMCProduct.HalfApprox.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T22:52:45.417674+00:00
-- url     : https://prove2.me/submissions/a67c1302-4b39-49ae-8f6e-4f16e4eaa2c2

import Mathlib
import Definitions.Def_QMCProduct_HalfApprox_Algorithm

open QMCProduct.HalfApprox QAlgorithms

namespace QMC12Aux

lemma kron_mul {n : ℕ} (A B : Fin n → Matrix Bool Bool ℂ) :
    kronAll A * kronAll B = kronAll (fun q => A q * B q) := by
  ext y z
  simp only [kronAll, Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]
  refine Fintype.sum_congr _ _ fun x => ?_
  rw [Finset.prod_mul_distrib]

lemma kron_one {n : ℕ} : kronAll (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext y z
  simp only [kronAll, Matrix.of_apply, Matrix.one_apply]
  by_cases h : y = z
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨q, hq⟩ : ∃ q, y q ≠ z q := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq])

variable {n : ℕ} (i j : Fin n)

def P2 (A B : Matrix Bool Bool ℂ) : Op n :=
  kronAll (fun q => if q = i then A else if q = j then B else 1)

lemma P2_mul (A B C D : Matrix Bool Bool ℂ) :
    P2 i j A B * P2 i j C D = P2 i j (A * C) (B * D) := by
  unfold P2; rw [kron_mul]; congr 1; funext q; split_ifs <;> simp

lemma P2_one : P2 i j (1 : Matrix Bool Bool ℂ) 1 = (1 : Op n) := by
  unfold P2; rw [← kron_one]; congr 1; funext q; split_ifs <;> rfl

lemma P2_smul (hij : i ≠ j) (c d : ℂ) (A B : Matrix Bool Bool ℂ) :
    P2 i j (c • A) (d • B) = (c * d) • P2 i j A B := by
  ext y z
  simp only [P2, kronAll, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have h : ∀ q, (if q = i then c • A else if q = j then d • B else 1) (y q) (z q) =
      ((if q = i then c else 1) * (if q = j then d else 1)) *
        (if q = i then A else if q = j then B else 1) (y q) (z q) := by
    intro q
    by_cases h1 : q = i
    · subst h1; simp [hij]
    · by_cases h2 : q = j
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [Finset.prod_congr rfl (fun q _ => h q), Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp

lemma XX_eq (hij : i ≠ j) (A B : Matrix Bool Bool ℂ) :
    onSite i A * onSite j B = P2 i j A B := by
  unfold onSite P2; rw [kron_mul]; congr 1; funext q
  by_cases h1 : q = i
  · subst h1; simp [hij]
  · by_cases h2 : q = j
    · subst h2; simp [h1]
    · simp [h1, h2]

-- Pauli algebra on Bool
lemma xx : pauliX * pauliX = 1 := by
  ext a b; cases a <;> cases b <;> simp [pauliX, Matrix.mul_apply]
lemma yy : pauliY * pauliY = 1 := by
  ext a b; cases a <;> cases b <;> simp [pauliY, Matrix.mul_apply]
lemma zz : pauliZ * pauliZ = 1 := by
  ext a b; cases a <;> cases b <;> simp [pauliZ, Matrix.mul_apply]
lemma xy : pauliX * pauliY = Complex.I • pauliZ := by
  ext a b; cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
lemma yx : pauliY * pauliX = (-Complex.I) • pauliZ := by
  ext a b; cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
lemma yz : pauliY * pauliZ = Complex.I • pauliX := by
  ext a b; cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
lemma zy : pauliZ * pauliY = (-Complex.I) • pauliX := by
  ext a b; cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
lemma zx : pauliZ * pauliX = Complex.I • pauliY := by
  ext a b; cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]
lemma xz : pauliX * pauliZ = (-Complex.I) • pauliY := by
  ext a b; cases a <;> cases b <;> simp [pauliX, pauliY, pauliZ, Matrix.mul_apply]


lemma TT (hij : i ≠ j) :
    (P2 i j pauliX pauliX + P2 i j pauliY pauliY + P2 i j pauliZ pauliZ) *
      (P2 i j pauliX pauliX + P2 i j pauliY pauliY + P2 i j pauliZ pauliZ) =
    (3 : ℂ) • (1 : Op n) - (2 : ℂ) • (P2 i j pauliX pauliX + P2 i j pauliY pauliY +
      P2 i j pauliZ pauliZ) := by
  simp only [add_mul, mul_add, P2_mul, xx, yy, zz, xy, yx, yz, zy, zx, xz, P2_smul i j hij, P2_one,
    Complex.I_mul_I, neg_mul_neg]
  module

def str (a b : Fin 4) : PauliString n := fun q => if q = i then a else if q = j then b else 0

lemma pauliOp_str (a b : Fin 4) : pauliOp (str i j a b) = P2 i j (pauli1 a) (pauli1 b) := by
  unfold pauliOp P2 str; congr 1; funext q; split_ifs <;> simp [pauli1]

lemma deg_str (a b : Fin 4) : pauliDegree (str i j a b) ≤ 2 := by
  unfold pauliDegree
  have h : Finset.univ.filter (fun q => str i j a b q ≠ 0) ⊆ {i, j} := by
    intro q hq
    rw [Finset.mem_filter] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hc; push_neg at hc
    exact hq.2 (by simp [str, hc.1, hc.2])
  exact (Finset.card_le_card h).trans Finset.card_le_two

lemma isPoly (k : ℕ) (hk : 2 ≤ k) (α : Fin 4 → ℝ) :
    IsPauliPoly k (∑ t : Fin 4, (α t : ℂ) • pauliOp (str i j t t)) := by
  refine ⟨fun s => ∑ t : Fin 4, if s = str i j t t then α t else 0, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
    by_cases h : s = str i j t t
    · subst h; exact (deg_str i j t t).trans hk
    · exact absurd (if_neg h) ht
  · simp only [Complex.ofReal_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]


theorem l5 {n k : ℕ} (hk : 2 ≤ k) (ρt : Op n)
    (hρ : IsPseudoDensity k ρt) (i j : Fin n) (hij : i ≠ j) :
    (0 ≤ mu ρt i j ∧ mu ρt i j ≤ 1) ∧
    (-(1 / 3 : ℝ) ≤ v ρt i j ∧ v ρt i j ≤ 1) ∧
    (-1 ≤ s ρt i j ∧ s ρt i j ≤ 1) := by
  set T := P2 i j pauliX pauliX + P2 i j pauliY pauliY + P2 i j pauliZ pauliZ with hT
  have hTT : T * T = (3 : ℂ) • (1 : Op n) - (2 : ℂ) • T := by rw [hT]; exact TT i j hij
  clear_value T
  have hsum : ∀ α : Fin 4 → ℝ, ∑ t : Fin 4, (α t : ℂ) • pauliOp (str i j t t) =
      (α 0 : ℂ) • (1 : Op n) + (α 1 : ℂ) • P2 i j pauliX pauliX +
        (α 2 : ℂ) • P2 i j pauliY pauliY + (α 3 : ℂ) • P2 i j pauliZ pauliZ := by
    intro α
    simp only [Fin.sum_univ_four, pauliOp_str]
    rw [show pauli1 0 = 1 by simp [pauli1], show pauli1 1 = pauliX by simp [pauli1],
      show pauli1 2 = pauliY by simp [pauli1], show pauli1 3 = pauliZ by simp [pauli1], P2_one]
  have key : ∀ α : Fin 4 → ℝ, (∀ P : Op n, P = ∑ t : Fin 4, (α t : ℂ) • pauliOp (str i j t t) →
      P * P = (4 : ℂ) • P) → 0 ≤ (ρt * ∑ t : Fin 4, (α t : ℂ) • pauliOp (str i j t t)).trace.re := by
    intro α hPP
    have h := hρ.2.2 _ (isPoly i j k hk α)
    rw [Matrix.mul_assoc, hPP _ rfl, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Complex.mul_re] at h
    have h4re : (4 : ℂ).re = 4 := by norm_num
    have h4im : (4 : ℂ).im = 0 := by norm_num
    rw [h4re, h4im, zero_mul, sub_zero] at h
    linarith
  have tr1 : (ρt * 1).trace = 1 := by rw [Matrix.mul_one]; exact hρ.2.1
  have hXX : X i * X j = P2 i j pauliX pauliX := XX_eq i j hij _ _
  have hYY : Y i * Y j = P2 i j pauliY pauliY := XX_eq i j hij _ _
  have hZZ : Z i * Z j = P2 i j pauliZ pauliZ := XX_eq i j hij _ _
  have e1 : ∑ t : Fin 4, (((if t = 0 then 1 else -1 : ℝ)) : ℂ) • pauliOp (str i j t t) =
      1 - T := by
    rw [hsum, hT]; simp; abel
  have e2 : ∑ t : Fin 4, (((if t = 0 then 3 else 1 : ℝ)) : ℂ) • pauliOp (str i j t t) =
      (3 : ℂ) • 1 + T := by
    rw [hsum, hT]; simp; abel
  have hup := key (fun t => if t = 0 then 1 else -1) (by
    intro P hP; rw [hP, e1, sub_mul, mul_sub, mul_sub, hTT, one_mul, mul_one, one_mul]
    module)
  have hlo := key (fun t => if t = 0 then 3 else 1) (by
    intro P hP
    rw [hP, e2, add_mul, mul_add, mul_add, hTT, smul_mul_smul_comm, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    module)
  rw [e1] at hup
  rw [e2] at hlo
  rw [hT] at hup hlo
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul, Complex.add_re, Complex.sub_re, Complex.mul_re, tr1,
    Complex.one_re, Complex.one_im] at hup hlo
  norm_num at hup hlo
  unfold mu v s val
  rw [hXX, hYY, hZZ]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

lemma trace_kron {n : ℕ} (M : Fin n → Matrix Bool Bool ℂ) :
    (kronAll M).trace = ∏ q, (M q).trace := by
  simp only [Matrix.trace, kronAll, Matrix.diag, Matrix.of_apply]
  rw [Fintype.prod_sum]

lemma trace_P2 (A B : Matrix Bool Bool ℂ) :
    (P2 (0 : Fin 2) 1 A B).trace = A.trace * B.trace := by
  unfold P2; rw [trace_kron, Fin.prod_univ_two]; simp

lemma trX : pauliX.trace = 0 := by simp [Matrix.trace, pauliX]
lemma trY : pauliY.trace = 0 := by simp [Matrix.trace, pauliY]
lemma trZ : pauliZ.trace = 0 := by simp [Matrix.trace, pauliZ]

end QMC12Aux

open QMC12Aux

theorem solution {n : ℕ} (ρt : Op n) (hρ : IsPseudoDensity 2 ρt) (i j : Fin n) (hij : i ≠ j) :
    (hQMC (0 : Fin 2) (1 : Fin 2) *
      ((1 / 4 : ℂ) • (1 - Z (0 : Fin 2) * Z (1 : Fin 2)))).trace.re = 1 / 2 ∧
    (1 / 2 : ℝ) * mu ρt i j ≤ 1 / 2 := by
  refine ⟨?_, ?_⟩
  · have h01 : (0 : Fin 2) ≠ 1 := by decide
    unfold hQMC
    rw [show X (0 : Fin 2) * X 1 = P2 0 1 pauliX pauliX from XX_eq _ _ h01 _ _, show Y (0 : Fin 2) * Y 1 = P2 0 1 pauliY pauliY from XX_eq _ _ h01 _ _,
      show Z (0 : Fin 2) * Z 1 = P2 0 1 pauliZ pauliZ from XX_eq _ _ h01 _ _]
    simp only [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, P2_mul, Matrix.one_mul,
      Matrix.mul_one, xx, yy, zz, xz, yz, zx, zy, xy, yx, P2_smul _ _ h01, P2_one,
      Matrix.trace_smul, Matrix.trace_sub, trace_P2, trX, trY, trZ, smul_eq_mul]
    simp [Matrix.trace_one, Fintype.card_fun]
    norm_num
  · have := (l5 (le_refl 2) ρt hρ i j hij).1.2
    linarith
