-- Prove2me | solution 1 for Representation.cayleyHamilton_of_frobeniusPowerDense
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ebb8d8e2-6120-5409-a261-5505160c6a87

import Mathlib
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_cayleyHamilton_of_frobeniusPowerDense

set_option autoImplicit false

p2m_open "Matrix P2MW.S_Representation_cayleyHamilton_of_frobeniusPowerDense.Matrix"

namespace Matrix
p2m_export "Matrix" "trace_sub ext sub_apply trace_smul det_one scalar trace_one trace_mul_comm det_fin_two det_mul one_apply smul_apply det det_pow of one mul_apply trace module trace_fin_two"
p2m_open "Matrix"

variable {R : Type*} [CommRing R]

theorem sq_eq_trace_smul_sub_det_smul_one' (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
    Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem pow_add_two_eq_trace_smul_sub_det_smul' (M : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    M ^ (k + 2) = M.trace • M ^ (k + 1) - M.det • M ^ k := by
  have h : M ^ (k + 2) = M ^ k * M ^ 2 := by rw [← pow_add]
  rw [h, sq_eq_trace_smul_sub_det_smul_one', Matrix.mul_sub, mul_smul_comm, mul_smul_comm,
    mul_one, ← pow_succ]

theorem trace_pow_add_two (M : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    (M ^ (k + 2)).trace = M.trace * (M ^ (k + 1)).trace - M.det * (M ^ k).trace := by
  rw [pow_add_two_eq_trace_smul_sub_det_smul', Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

end Matrix

noncomputable section

namespace CayleyHamiltonDensity

section Abstract

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B]

theorem sq_eq_of_quadRel {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    a * a = M.trace • a - M.det • (1 : B) :=
  sub_eq_zero.mp (by rw [← h]; abel)

theorem mul_compl_eq_det_smul_one {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    a * (M.trace • (1 : B) - a) = M.det • (1 : B) := by
  rw [mul_sub, mul_smul_comm, mul_one, sq_eq_of_quadRel h]
  abel

theorem compl_mul_eq_det_smul_one {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    (M.trace • (1 : B) - a) * a = M.det • (1 : B) := by
  rw [sub_mul, smul_mul_assoc, one_mul, sq_eq_of_quadRel h]
  abel

theorem commute_complRoot {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    Commute a (M.trace • (1 : B) - a) := by
  unfold Commute SemiconjBy
  rw [mul_compl_eq_det_smul_one h, compl_mul_eq_det_smul_one h]

theorem pow_add_compl_pow_eq_trace_pow_smul_one {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) (m : ℕ) :
    a ^ m + (M.trace • (1 : B) - a) ^ m = (M ^ m).trace • (1 : B) := by
  set b : B := M.trace • (1 : B) - a with hb
  have hsum : a + b = M.trace • (1 : B) := by rw [hb]; abel
  have hcomm : Commute a b := commute_complRoot h
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 =>
      simp only [pow_zero, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, two_smul]
    | 1 =>
      simp only [pow_one, hsum]
    | (m + 2) =>

      have hc1 : b * a ^ (m + 1) = a ^ (m + 1) * b := (hcomm.symm.pow_right (m + 1)).eq
      have hc2 : b * a ^ m = a ^ m * b := (hcomm.symm.pow_right m).eq
      have hrec : a ^ (m + 2) + b ^ (m + 2)
          = (a + b) * (a ^ (m + 1) + b ^ (m + 1)) - (a * b) * (a ^ m + b ^ m) := by
        have e1 : (a + b) * (a ^ (m + 1) + b ^ (m + 1))
            = a ^ (m + 2) + a * b ^ (m + 1) + (a ^ (m + 1) * b + b ^ (m + 2)) := by
          rw [add_mul, mul_add, mul_add, ← pow_succ', ← pow_succ', hc1]
        have e2 : (a * b) * (a ^ m + b ^ m)
            = a ^ (m + 1) * b + a * b ^ (m + 1) := by
          rw [mul_add, mul_assoc a b (a ^ m), hc2, ← mul_assoc, ← pow_succ',
            mul_assoc a b (b ^ m), ← pow_succ']
        rw [e1, e2]
        abel
      rw [hrec, ih (m + 1) (by omega), ih m (by omega), hsum,
        mul_compl_eq_det_smul_one h, smul_mul_smul_comm, smul_mul_smul_comm, mul_one,
        ← sub_smul, ← Matrix.trace_pow_add_two]

theorem quadRel_pow {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) (n : ℕ) :
    a ^ n * a ^ n - (M ^ n).trace • a ^ n + (M ^ n).det • (1 : B) = 0 := by
  set b : B := M.trace • (1 : B) - a with hb
  have hcomm : Commute a b := commute_complRoot h

  have hsum : (M ^ n).trace • (1 : B) = a ^ n + b ^ n :=
    (pow_add_compl_pow_eq_trace_pow_smul_one h n).symm

  have hprod : (M ^ n).det • (1 : B) = a ^ n * b ^ n := by
    rw [← hcomm.mul_pow, hb, mul_compl_eq_det_smul_one h, smul_pow, one_pow,
      Matrix.det_pow]

  have hsmul : (M ^ n).trace • a ^ n = ((M ^ n).trace • (1 : B)) * a ^ n := by
    rw [smul_mul_assoc, one_mul]
  rw [hsmul, hsum, hprod, add_mul, (hcomm.pow_pow n n).eq]
  abel

theorem quadRel_conj {a u v : B} (huv : u * v = 1) (hvu : v * u = 1)
    {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    (u * a * v) * (u * a * v) - M.trace • (u * a * v) + M.det • (1 : B) = 0 := by
  have key : (u * a * v) * (u * a * v) - M.trace • (u * a * v) + M.det • (1 : B)
      = u * (a * a - M.trace • a + M.det • (1 : B)) * v := by
    have e1 : (u * a * v) * (u * a * v) = u * (a * a) * v := by
      calc (u * a * v) * (u * a * v) = u * a * (v * u) * a * v := by
            simp only [mul_assoc]
        _ = u * (a * a) * v := by rw [hvu, mul_one, mul_assoc u a a]
    have e2 : M.trace • (u * a * v) = u * (M.trace • a) * v := by
      rw [mul_smul_comm, smul_mul_assoc]
    have e3 : M.det • (1 : B) = u * (M.det • (1 : B)) * v := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, huv]
    rw [mul_add, add_mul, mul_sub, sub_mul, ← e1, ← e2, ← e3]
  rw [key, h, mul_zero, zero_mul]

end Abstract

section MatrixConj

variable {k : Type*} [CommRing k]

theorem trace_matrix_conj {P Q : Matrix (Fin 2) (Fin 2) k} (hQP : Q * P = 1)
    (N : Matrix (Fin 2) (Fin 2) k) : (P * N * Q).trace = N.trace := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, hQP, one_mul]

theorem det_matrix_conj {P Q : Matrix (Fin 2) (Fin 2) k} (hPQ : P * Q = 1)
    (N : Matrix (Fin 2) (Fin 2) k) : (P * N * Q).det = N.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm P.det, mul_assoc, ← Matrix.det_mul, hPQ,
    Matrix.det_one, mul_one]

end MatrixConj

section DensityStep

theorem apply_eq_of_mul_inv_mem_ker {G M : Type*} [Group G] [Monoid M] (f : G →* M)
    {x σ : G} (h : x * σ⁻¹ ∈ f.ker) : f σ = f x := by
  have h1 : f x * f σ⁻¹ = 1 := by rw [← map_mul]; exact h
  have h2 : f σ⁻¹ * f σ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc f σ = (f x * f σ⁻¹) * f σ := by rw [h1, one_mul]
    _ = f x * (f σ⁻¹ * f σ) := mul_assoc _ _ _
    _ = f x := by rw [h2, mul_one]

theorem apply_mul_apply_inv_cancel {G M : Type*} [Group G] [Monoid M] (f : G →* M) (g : G) :
    f g * f g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem apply_inv_mul_apply_cancel {G M : Type*} [Group G] [Monoid M] (f : G →* M) (g : G) :
    f g⁻¹ * f g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]

theorem cayleyHamilton_of_frobeniusPowerDense_aux
    (ρV : Representation k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k)
    {S : Finset ℕ}
    (hCH : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          ρV τ * ρV τ - (ρ τ).trace • ρV τ + (ρ τ).det • (1 : Module.End k V) = 0)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ ρV.ker))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρV σ * ρV σ - (ρ σ).trace • ρV σ + (ρ σ).det • (1 : Module.End k V) = 0 := by
  obtain ⟨ℓ, A, τ, g, n, hℓ, hS, hA, hτ, hmem⟩ := hdense σ

  have keyρ : ρ σ = ρ g * (ρ τ) ^ n * ρ g⁻¹ := by
    rw [apply_eq_of_mul_inv_mem_ker ρ (Subgroup.mem_inf.mp hmem).1, map_mul, map_mul,
      map_pow]
  have keyρV : ρV σ = ρV g * (ρV τ) ^ n * ρV g⁻¹ := by
    rw [apply_eq_of_mul_inv_mem_ker ρV (Subgroup.mem_inf.mp hmem).2, map_mul, map_mul,
      map_pow]

  have htr : (ρ σ).trace = ((ρ τ) ^ n).trace := by
    rw [keyρ, trace_matrix_conj (apply_inv_mul_apply_cancel ρ g)]
  have hdet : (ρ σ).det = ((ρ τ) ^ n).det := by
    rw [keyρ, det_matrix_conj (apply_mul_apply_inv_cancel ρ g)]

  have hpow : (ρV τ) ^ n * (ρV τ) ^ n - ((ρ τ) ^ n).trace • (ρV τ) ^ n
      + ((ρ τ) ^ n).det • (1 : Module.End k V) = 0 :=
    quadRel_pow (hCH ℓ hℓ hS A hA τ hτ) n

  rw [htr, hdet, keyρV]
  exact quadRel_conj (apply_mul_apply_inv_cancel ρV g) (apply_inv_mul_apply_cancel ρV g) hpow

end DensityStep

end CayleyHamiltonDensity

end

theorem solution {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]
    (ρV : Representation k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k)
    {S : Finset ℕ}
    (hCH : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          ρV τ * ρV τ - (ρ τ).trace • ρV τ + (ρ τ).det • (1 : Module.End k V) = 0)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ ρV.ker))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρV σ * ρV σ - (ρ σ).trace • ρV σ + (ρ σ).det • (1 : Module.End k V) = 0 :=
  CayleyHamiltonDensity.cayleyHamilton_of_frobeniusPowerDense_aux ρV ρ hCH hdense σ

end S_Representation_cayleyHamilton_of_frobeniusPowerDense
end P2MW
export P2MW.S_Representation_cayleyHamilton_of_frobeniusPowerDense (solution)
