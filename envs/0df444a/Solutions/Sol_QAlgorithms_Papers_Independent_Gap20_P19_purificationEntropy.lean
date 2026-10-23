-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.purificationEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:03:20.484824+00:00
-- url     : https://prove2.me/submissions/344b1691-f9d2-4e4f-a8ba-2965eb767015

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Matrix Polynomial

theorem x8_tr_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℝ[X]) :
    (aeval M p).trace = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (M ^ i).trace := by
  rw [aeval_eq_sum_range, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul]
  simp [Complex.real_smul]

theorem x8_tr_cfc_eq {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M1 : Matrix ι ι ℂ) (M2 : Matrix κ κ ℂ) (h1 : M1.IsHermitian) (h2 : M2.IsHermitian)
    (h : ∀ k : ℕ, 1 ≤ k → (M1 ^ k).trace = (M2 ^ k).trace) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f M1).trace = (cfc f M2).trace := by
  classical
  let S : Finset ℝ := Finset.univ.image h1.eigenvalues ∪ Finset.univ.image h2.eigenvalues ∪ {0}
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have e1 : cfc f M1 = cfc (fun x => p.eval x) M1 := by
    apply cfc_congr
    intro x hx
    rw [h1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have e2 : cfc f M2 = cfc (fun x => p.eval x) M2 := by
    apply cfc_congr
    intro x hx
    rw [h2.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hp 0 (by simp [S]), hf]
  rw [e1, e2, cfc_polynomial p M1, cfc_polynomial p M2, x8_tr_aeval, x8_tr_aeval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [h0]
  · rw [h i hi]

theorem x8_pow_mul {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) :
    (V * W) ^ (k + 1) = V * (W * V) ^ k * W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

theorem x8_tr_pow_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ((V * W) ^ k).trace = ((W * V) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [x8_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

/-- tr f(V Vᴴ) = tr f((Vᴴ V)ᵀ) when f 0 = 0. -/
theorem x8_ent_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) :
    QAlgorithms.vnEntropy (V * Vᴴ) = QAlgorithms.vnEntropy ((Vᴴ * V)ᵀ) := by
  unfold QAlgorithms.vnEntropy
  rw [x8_tr_cfc_eq (V * Vᴴ) ((Vᴴ * V)ᵀ) (isHermitian_mul_conjTranspose_self V)
    (isHermitian_conjTranspose_mul_self V).transpose _ _ (by simp)]
  intro k hk
  rw [← Matrix.transpose_pow, Matrix.trace_transpose, x8_tr_pow_swap _ _ k hk]

namespace QAlgorithms.Papers.Independent.Gap20.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem x8_M1 {A B E R : Type} [Fintype A] [Fintype B] [Fintype E] [Fintype R]
    (U : Matrix (B × E) A ℂ) (chi : EuclideanSpace ℂ (R × A)) :
    idTensorSuperop (receiverChannel U) (pureDensity chi) =
      (Matrix.of fun (x : R × B) (e : E) => ∑ a, U (x.2, e) a * chi (x.1, a)) *
      (Matrix.of fun (x : R × B) (e : E) => ∑ a, U (x.2, e) a * chi (x.1, a))ᴴ := by
  ext ⟨r, b⟩ ⟨r', b'⟩
  simp only [idTensorSuperop, receiverChannel, traceRight, pureDensity, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul', Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun a' _ => ?_
  simp only [RCLike.star_def]; ring

theorem x8_M2 {A B E R : Type} [Fintype A] [Fintype B] [Fintype E] [Fintype R]
    (U : Matrix (B × E) A ℂ) (chi : EuclideanSpace ℂ (R × A)) :
    complementaryChannel U (traceLeft (pureDensity chi)) =
      ((Matrix.of fun (x : R × B) (e : E) => ∑ a, U (x.2, e) a * chi (x.1, a))ᴴ *
      (Matrix.of fun (x : R × B) (e : E) => ∑ a, U (x.2, e) a * chi (x.1, a)))ᵀ := by
  ext e e'
  simp only [complementaryChannel, traceLeft, pureDensity, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul', Finset.sum_mul,
    Finset.mul_sum, Fintype.sum_prod_type]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => arg 2; ext x; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [RCLike.star_def]; ring

end QAlgorithms.Papers.Independent.Gap20.P19



open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open Filter Topology

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
   maximumCoherentInformation dilationPower)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (MinimalDilation indexedKrausDilation arbitraryVectorComplement superopTensor tensorDilation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P69 (choi)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E F R K A2 B2 E2 : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype E] [DecidableEq E] [Nonempty E]

variable [Fintype F] [DecidableEq F] [Nonempty F]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype K] [DecidableEq K]

variable [Fintype A2] [DecidableEq A2] [Nonempty A2]

variable [Fintype B2] [DecidableEq B2] [Nonempty B2]

variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P19 in
/-- Appendix A.2, PDF p.26, (69)–(71): purification output entropy equals
complement entropy. Both coherent-information definitions consequently agree. -/
theorem solution [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty R]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U)
    (chi : EuclideanSpace ℂ (R × A)) (hchi : IsState chi) :
    let rho := traceLeft (pureDensity chi)
    vnEntropy (idTensorSuperop (receiverChannel U) (pureDensity chi)) =
      vnEntropy (complementaryChannel U rho) ∧
    vnEntropy (receiverChannel U rho) -
      vnEntropy (idTensorSuperop (receiverChannel U) (pureDensity chi)) = coherentAt U rho :=
  by
    intro rho
    have h1 : vnEntropy (idTensorSuperop (receiverChannel U) (pureDensity chi)) =
        vnEntropy (complementaryChannel U rho) := by
      rw [x8_M1, x8_M2]; exact x8_ent_swap _
    exact ⟨h1, by rw [h1]; rfl⟩



