-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.dephasingSeparation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T23:56:03.161266+00:00
-- url     : https://prove2.me/submissions/c0eaedf6-795f-44ab-b770-6ae7df7fe5cb

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

-- ===== P41DS =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Entanglement (IsCompletelyPositive)
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)
open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4P41D
open Matrix

lemma cfc_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  classical
  let S : Finset ℝ := Finset.univ.image d
  let p : Polynomial ℝ := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have hD : IsSelfAdjoint (diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1; funext i; simp
  have hspec : ∀ x ∈ spectrum ℝ (diagonal (fun i => (d i : ℂ))), x ∈ S := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, spectrum_diagonal] at hx
    obtain ⟨i, hi⟩ := hx
    have : d i = x := by simpa using hi
    simp [S, ← this]
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x (hspec x hx)).symm),
    cfc_polynomial p _ hD]
  have : Polynomial.aeval (diagonal (fun i => (d i : ℂ))) p =
      diagonal (Polynomial.aeval (fun i => (d i : ℂ)) p) :=
    (Polynomial.aeval_algHom_apply (diagonalAlgHom ℝ) (fun i => (d i : ℂ)) p)
  rw [this, Polynomial.aeval_pi_apply]
  congr 1; funext i
  have h := Polynomial.aeval_algebraMap_apply ℂ (d i) p
  simp only [Complex.coe_algebraMap] at h
  rw [h, Polynomial.coe_aeval_eq_eval, hp _ (by simp [S] : d i ∈ S)]

lemma deph_kraus {d : ℕ} :
    (dephasing : Superop (Fin d) (Fin d)) =
      krausApply (fun k : Fin d => Matrix.single k k (1 : ℂ)) := by
  funext X
  ext i j
  simp only [dephasing, krausApply, Matrix.sum_apply, diagonal_apply]
  simp only [Matrix.single_mul_mul_single, conjTranspose_single, star_one, one_mul,
    Matrix.single_apply]
  by_cases h : i = j
  · subst h; rw [Finset.sum_eq_single i] <;> simp_all
  · rw [if_neg h]
    exact (Finset.sum_eq_zero fun (x : Fin d) _ =>
      if_neg (by rintro ⟨h1, h2⟩; exact h (h1.symm.trans h2))).symm

end X4P41D

theorem solution {d a : ℕ} [NeZero d] (p : Fin d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (htotal : ∑ i, p i = 1)
    (hmixed : ∃ i j, i ≠ j ∧ 0 < p i ∧ 0 < p j)
    (psi : EuclideanSpace ℂ (Fin a × Fin d))
    (hpsi : IsPurification (Matrix.diagonal fun i => (p i : ℂ)) psi) :
    let rho := Matrix.diagonal fun i => (p i : ℂ)
    dephasing rho = rho ∧ rootFidelity rho (dephasing rho)^2 = 1 ∧
      purificationFidelity psi dephasing = ∑ i, (p i)^2 ∧
      purificationFidelity psi dephasing < 1 := by
  intro rho
  have hdeph : dephasing rho = rho := by
    ext i j
    simp only [dephasing, rho, Matrix.diagonal_apply]
    by_cases h : i = j <;> simp [h]
  have hfid : purificationFidelity psi dephasing = ∑ i, (p i)^2 := by
    rw [X4P41D.deph_kraus, X4P41L.kraus_fid, hpsi.2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_mul_single]
    simp [Complex.normSq_ofReal, sq]
  refine ⟨hdeph, ?_, hfid, ?_⟩
  · rw [hdeph]
    simp only [rootFidelity, rho]
    rw [X4P41D.cfc_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    have : (fun i => ((Real.sqrt (p i) : ℝ) : ℂ) * (p i : ℂ) * ((Real.sqrt (p i) : ℝ) : ℂ)) =
        fun i => (((p i) ^ 2 : ℝ) : ℂ) := by
      funext i
      have := Real.mul_self_sqrt (hp i)
      have h2 : ((Real.sqrt (p i) : ℝ) : ℂ) * ((Real.sqrt (p i) : ℝ) : ℂ) = (p i : ℂ) := by
        exact_mod_cast this
      push_cast
      linear_combination (p i : ℂ) * h2
    rw [this, X4P41D.cfc_diag, Matrix.trace_diagonal]
    simp only [Real.sqrt_sq (hp _)]
    rw [← Complex.ofReal_sum, Complex.ofReal_re, htotal]; norm_num
  · rw [hfid]
    obtain ⟨i, j, hij, hi, hj⟩ := hmixed
    have hle : ∀ k, p k ≤ 1 := fun k => by
      rw [← htotal]
      exact Finset.single_le_sum (fun l _ => hp l) (Finset.mem_univ k)
    have hi1 : p i < 1 := by
      have : p i + p j ≤ 1 := by
        rw [← htotal, ← Finset.sum_pair hij]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun l _ _ => hp l)
      linarith
    rw [← htotal]
    refine Finset.sum_lt_sum (fun k _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · nlinarith [hp k, hle k]
    · nlinarith

#print axioms solution
