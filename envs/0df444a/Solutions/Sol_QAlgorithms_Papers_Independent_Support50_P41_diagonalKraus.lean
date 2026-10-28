-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.diagonalKraus
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:09:03.864639+00:00
-- url     : https://prove2.me/submissions/c363d06a-c827-4b2e-9c6c-7ea0efd9ea78

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

-- ===== P41DK =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4P41K
open Matrix

variable {d m : ℕ}

/-- unitary mixing of Kraus operators -/
def mix (V : Matrix (Fin m) (Fin m) ℂ) (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (k : Fin m) :
    Matrix (Fin d) (Fin d) ℂ := ∑ l, conj (V l k) • E l

lemma mix_ct (V : Matrix (Fin m) (Fin m) ℂ) (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (k : Fin m) :
    (mix V E k)ᴴ = ∑ l, V l k • (E l)ᴴ := by
  simp [mix, conjTranspose_sum, conjTranspose_smul]

lemma VVh (V : Matrix (Fin m) (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ) (l l' : Fin m) :
    ∑ k, V l k * conj (V l' k) = if l = l' then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hV) l) l'
  simp only [Matrix.mul_apply, star_apply, RCLike.star_def, one_apply] at h
  exact h

lemma perm3 {α : Type*} [AddCommMonoid α] (f : Fin m → Fin m → Fin m → α) :
    (∑ k, ∑ l, ∑ l', f k l l') = ∑ l, ∑ l', ∑ k, f k l l' := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_comm

lemma collapse {α : Type*} [AddCommGroup α] [Module ℂ α] (V : Matrix (Fin m) (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ) (M : Fin m → Fin m → α) :
    (∑ l, ∑ l', ∑ k, (V l k * conj (V l' k)) • M l l') = ∑ l, M l l := by
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [← Finset.sum_smul, VVh V hV, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq]; simp

lemma mix_kraus (V : Matrix (Fin m) (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ k, (mix V E k)ᴴ * X * mix V E k = ∑ l, (E l)ᴴ * X * E l := by
  have expand : ∀ k, (mix V E k)ᴴ * X * mix V E k =
      ∑ l, ∑ l', (V l' k * conj (V l k)) • ((E l')ᴴ * X * E l) := by
    intro k
    rw [mix_ct]
    simp only [mix, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    rw [mul_comm (V l' k)]
  simp_rw [expand]
  rw [perm3, Finset.sum_comm, collapse V hV (fun a b => (E a)ᴴ * X * E b)]

lemma mix_act (V : Matrix (Fin m) (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ k, mix V E k * X * (mix V E k)ᴴ = ∑ l, E l * X * (E l)ᴴ := by
  have expand : ∀ k, mix V E k * X * (mix V E k)ᴴ =
      ∑ l, ∑ l', (V l k * conj (V l' k)) • (E l' * X * (E l)ᴴ) := by
    intro k
    rw [mix_ct]
    simp only [mix, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
      Finset.smul_sum]
  simp_rw [expand]
  rw [perm3, collapse V hV (fun l l' => E l' * X * (E l)ᴴ)]

theorem main (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    ∃ m : ℕ, ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
      OperatorSum Phi A ∧ ∀ k l, k ≠ l → (A k * rho * (A l)ᴴ).trace = 0 := by
  obtain ⟨m, E, hK, hE⟩ := hPhi
  let W : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun k l => (E k * rho * (E l)ᴴ).trace
  have hW : W.IsHermitian := by
    ext k l
    rw [conjTranspose_apply]
    simp only [W, Matrix.of_apply]
    rw [← Matrix.trace_conjTranspose]
    congr 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, conjTranspose_conjTranspose,
      hrho.1.1.eq, Matrix.mul_assoc]
  set V := (hW.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  have hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ := hW.eigenvectorUnitary.2
  have hspec := hW.spectral_theorem
  have hD : star V * W * V = diagonal (RCLike.ofReal ∘ hW.eigenvalues) := by
    conv_lhs => rw [hspec]
    simp only [Unitary.conjStarAlgAut_apply]
    have h1 : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
    simp only [V] at h1 ⊢
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
      Matrix.mul_one]
  refine ⟨m, mix V E, ⟨?_, fun X => ?_⟩, fun k l hkl => ?_⟩
  · unfold IsKrausFamily
    have := mix_kraus V hV E 1
    simp only [Matrix.mul_one] at this
    rw [this]; exact hK
  · rw [hE X, krausApply, krausApply, mix_act V hV E X]
  · have := congrFun (congrFun hD k) l
    rw [diagonal_apply_ne _ hkl] at this
    rw [← this, mix_ct]
    simp only [mix, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Matrix.mul_apply, star_apply,
      RCLike.star_def, W, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

end X4P41K

theorem solution {d : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    ∃ m : ℕ, ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
      OperatorSum Phi A ∧ ∀ k l, k ≠ l → (A k * rho * (A l)ᴴ).trace = 0 :=
  X4P41K.main Phi hPhi rho hrho

#print axioms solution
