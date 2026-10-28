-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.krausFidelity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T23:53:55.261624+00:00
-- url     : https://prove2.me/submissions/0ae3c6b9-1af2-42e7-b474-cf5d582820bc

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

-- ===== P41Lib =====

noncomputable section

namespace X4P41L

open QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity
  complexQuadraticForm)
open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)
open scoped Matrix ComplexConjugate
open Matrix

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {a d m : ℕ}

/-- the Kraus-branch vectors -/
def phi (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (psi : EuclideanSpace ℂ (Fin a × Fin d))
    (k : Fin m) : EuclideanSpace ℂ (Fin a × Fin d) :=
  WithLp.toLp 2 fun p => ∑ i, A k p.2 i * psi (p.1, i)

lemma idTensor_kraus (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) :
    idTensorSuperop (krausApply A) (pureDensity psi) = ∑ k, pureDensity (phi A psi k) := by
  ext p q
  simp only [idTensorSuperop, krausApply, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    pureDensity, conjTranspose_apply, phi, PiLp.toLp_apply, map_sum, map_mul, RCLike.star_def,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma cqf_sum {ι K : Type*} [Fintype ι] [Fintype K] (v : EuclideanSpace ℂ ι)
    (M : K → Matrix ι ι ℂ) :
    complexQuadraticForm v (∑ k, M k) = ∑ k, complexQuadraticForm v (M k) := by
  simp only [complexQuadraticForm, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm), Finset.sum_comm]

lemma cqf_pure {ι : Type*} [Fintype ι] (v w : EuclideanSpace ℂ ι) :
    complexQuadraticForm v (pureDensity w) = (Complex.normSq (∑ x, conj (v x) * w x) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [complexQuadraticForm, pureDensity, Matrix.of_apply, map_sum, map_mul,
    Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma overlap_trace (A : Matrix (Fin d) (Fin d) ℂ) (psi : EuclideanSpace ℂ (Fin a × Fin d))
    (k : Fin m) (B : Fin m → Matrix (Fin d) (Fin d) ℂ) (hB : B k = A) :
    ∑ x, conj (psi x) * phi B psi k x = (traceLeft (pureDensity psi) * A).trace := by
  simp only [phi, PiLp.toLp_apply, hB, Matrix.trace, Matrix.diag, Matrix.mul_apply, traceLeft,
    pureDensity, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
  ring

theorem kraus_fid (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) :
    purificationFidelity psi (krausApply A) =
      ∑ k, Complex.normSq ((traceLeft (pureDensity psi) * A k).trace) := by
  unfold purificationFidelity
  rw [idTensor_kraus, cqf_sum]
  simp_rw [cqf_pure]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [overlap_trace (A k) psi k A rfl]

lemma choi_rel {d : ℕ} (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Fin d)) :
    Phi (pureDensity v) = relativeOperator (indexState v) (choi Phi) := by
  have hv : pureDensity v = ∑ i, ∑ l, (v i * conj (v l)) • Matrix.single i l (1 : ℂ) := by
    ext x y
    simp only [pureDensity, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single y]
      · simp
      · intro b _ hb; simp [Ne.symm hb, hb]
      · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      simp [Ne.symm hb, hb]
    · simp
  ext j k
  rw [hv]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    relativeOperator, indexState, PiLp.toLp_apply, Complex.conj_conj, choi]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end X4P41L

-- ===== P41KF =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Entanglement (IsCompletelyPositive)
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)
open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem solution {d a m : ℕ} [NeZero d]
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi)
    (Phi : Superop (Fin d) (Fin d)) (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hA : OperatorSum Phi A) :
    purificationFidelity psi Phi = ∑ k, Complex.normSq ((rho * A k).trace) := by
  have hPhi : Phi = krausApply A := funext hA.2
  rw [hPhi, X4P41L.kraus_fid, hpsi.2]

end

#print axioms solution
