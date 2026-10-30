-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P18.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:15:07.175142+00:00
-- url     : https://prove2.me/submissions/6063fcda-df0f-42d4-9f99-2afe3fd3685f

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18
namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

theorem s110c07_single (y a z b : Bool) :
    ∑ j : Fin 4, (sourcePauli j).mat y a * conj ((sourcePauli j).mat z b) =
      if y = z ∧ a = b then 2 else 0 := by
  cases y <;> cases a <;> cases z <;> cases b <;>
    simp [Fin.sum_univ_four, sourcePauli, Stabilizer.Pauli.mat, QAlgorithms.pauliX,
      QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.diagonal] <;> norm_num

theorem s110c07_unit1 (P : Stabilizer.Pauli) (y z : Bool) :
    ∑ a : Bool, P.mat y a * conj (P.mat z a) = if y = z then 1 else 0 := by
  cases P <;> cases y <;> cases z <;>
    simp [Stabilizer.Pauli.mat, QAlgorithms.pauliX,
      QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.diagonal, Matrix.one_apply]

theorem s110c07_entry {n : ℕ} (x : Fin n → Fin 4) (y z : QAlgorithms.Qubits n) :
    (Stabilizer.PauliString.mk 0 (fun j => sourcePauli (x j))).toMatrix y z =
      ∏ q, (sourcePauli (x q)).mat (y q) (z q) := by
  simp [Stabilizer.PauliString.toMatrix]

theorem s110c07_unitary {n : ℕ} (x : Fin n → Fin 4) :
    (Stabilizer.PauliString.mk 0 (fun j => sourcePauli (x j))).toMatrix ∈
      Matrix.unitaryGroup (QAlgorithms.Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext y z
  simp only [Matrix.mul_apply, Matrix.star_apply, s110c07_entry, Matrix.one_apply]
  have : ∀ a : QAlgorithms.Qubits n, (∏ q, (sourcePauli (x q)).mat (y q) (a q)) *
      star (∏ q, (sourcePauli (x q)).mat (z q) (a q)) =
      ∏ q, ((sourcePauli (x q)).mat (y q) (a q) * conj ((sourcePauli (x q)).mat (z q) (a q))) := by
    intro a; rw [star_prod, ← Finset.prod_mul_distrib]; rfl
  simp only [this]
  rw [← Fintype.prod_sum (fun q (c : Bool) =>
    (sourcePauli (x q)).mat (y q) c * conj ((sourcePauli (x q)).mat (z q) c))]
  simp only [s110c07_unit1]
  by_cases h : y = z
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

theorem s110c07_twirl {n : ℕ} (y a z b : QAlgorithms.Qubits n) :
    ∑ x : Fin n → Fin 4, (∏ q, (sourcePauli (x q)).mat (y q) (a q)) *
      conj (∏ q, (sourcePauli (x q)).mat (z q) (b q)) =
      if y = z ∧ a = b then (2 : ℂ) ^ n else 0 := by
  have : ∀ x : Fin n → Fin 4, (∏ q, (sourcePauli (x q)).mat (y q) (a q)) *
      conj (∏ q, (sourcePauli (x q)).mat (z q) (b q)) =
      ∏ q, ((sourcePauli (x q)).mat (y q) (a q) * conj ((sourcePauli (x q)).mat (z q) (b q))) := by
    intro x; rw [map_prod, ← Finset.prod_mul_distrib]
  simp only [this]
  rw [← Fintype.prod_sum (fun q (j : Fin 4) =>
    (sourcePauli j).mat (y q) (a q) * conj ((sourcePauli j).mat (z q) (b q)))]
  simp only [s110c07_single]
  by_cases h : y = z ∧ a = b
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h]
    have : ∃ q, ¬ (y q = z q ∧ a q = b q) := by
      by_contra hc; push Not at hc
      exact h ⟨funext fun q => (hc q).1, funext fun q => (hc q).2⟩
    obtain ⟨q, hq⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

theorem s110c07_enc {n : ℕ} (rho : Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ) :
    encrypt (fullPauli n) rho = (((2 : ℂ) ^ n)⁻¹ * rho.trace) • 1 := by
  ext y z
  simp only [encrypt, fullPauli, Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, s110c07_entry, smul_eq_mul, Matrix.one_apply]
  have h1 : ∀ x : Fin n → Fin 4,
      (∑ b, (∑ a, (∏ q, (sourcePauli (x q)).mat (y q) (a q)) * rho a b) *
        star (∏ q, (sourcePauli (x q)).mat (z q) (b q))) =
      ∑ a, ∑ b, rho a b * ((∏ q, (sourcePauli (x q)).mat (y q) (a q)) *
        conj (∏ q, (sourcePauli (x q)).mat (z q) (b q))) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [RCLike.star_def]; ring
  simp only [h1, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ a : QAlgorithms.Qubits n, (∑ x : Fin n → Fin 4, ∑ b, rho a b *
      ((∏ q, (sourcePauli (x q)).mat (y q) (a q)) *
        conj (∏ q, (sourcePauli (x q)).mat (z q) (b q)))) =
      ∑ b, rho a b * (if y = z ∧ a = b then (2 : ℂ) ^ n else 0) := by
    intro a
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, s110c07_twirl]
  simp only [h2]
  by_cases hyz : y = z
  · simp only [hyz, true_and, if_true, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      Matrix.trace, Matrix.diag]
    rw [← Finset.sum_mul]
    push_cast
    rw [pow_mul]
    field_simp
    ring_nf
    rw [pow_mul]; norm_num
    left; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  · simp [hyz]

open scoped ComplexOrder in
theorem s110c07_mixed (n : ℕ) : IsDensityMatrix (sourceMixedIdentity (QAlgorithms.Qubits n)) := by
  unfold sourceMixedIdentity
  refine ⟨?_, ?_⟩
  · apply Matrix.PosSemidef.smul Matrix.PosSemidef.one
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have : ((2 ^ n : ℕ) : ℂ)⁻¹ = (((2 ^ n : ℕ) : ℝ)⁻¹ : ℝ) := by push_cast; rfl
    rw [this]
    exact Complex.zero_le_real.mpr (inv_nonneg.mpr (by positivity))
  · rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    have : (Fintype.card (QAlgorithms.Qubits n) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp

end

end QAlgorithms.Papers.Independent.Advance50.P18

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P18

theorem solution (n : ℕ) :
    BarePQC (allPure (Qubits n)) (fullPauli n) (sourceMixedIdentity (Qubits n)) := by
  refine ⟨⟨fun _ => by simp [fullPauli], ?_, fun x => s110c07_unitary x⟩,
    s110c07_mixed n, fun psi hpsi => ⟨hpsi, ?_⟩⟩
  · simp only [fullPauli, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    rw [pow_mul]; norm_num
  · rw [s110c07_enc]
    have ht : (pureDensity psi).trace = 1 := by
      have h := hpsi
      unfold allPure IsState at h
      simp only [Set.mem_ofPred_eq] at h
      simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply, Complex.mul_conj]
      have := EuclideanSpace.norm_eq psi
      rw [h, eq_comm, Real.sqrt_eq_one] at this
      rw [← Complex.ofReal_one, ← this]; push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [ht, mul_one]
    unfold sourceMixedIdentity
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; rfl
