-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P35.operator_basis_isometry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:17:15.975984+00:00
-- url     : https://prove2.me/submissions/37fc80d0-d140-40c3-9fbd-a9d5449e8c7b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

-- ===== P35B =====

noncomputable section

namespace X4OB
open Matrix QAlgorithms.Papers.Independent.Support50.P35
open scoped Matrix ComplexConjugate

variable {I K L : Type*} [Fintype I] [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]

lemma tr_real {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (((A * B).trace.re : ℝ) : ℂ) = (A * B).trace := by
  have h : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.1 h

lemma coeff {nu : L → Matrix I I ℂ} (hnu : IsHermitianONBasis nu) (c : L → ℝ) (l' : L) :
    ((∑ l, (c l : ℂ) • nu l) * nu l').trace.re = c l' := by
  rw [Finset.sum_mul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, hnu.2.1, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.ofReal_re]

lemma expand {mu : K → Matrix I I ℂ} {nu : L → Matrix I I ℂ} (hmu : IsHermitianONBasis mu)
    (hnu : IsHermitianONBasis nu) (k : K) :
    mu k = ∑ l, ((basisChange nu mu l k : ℝ) : ℂ) • nu l := by
  obtain ⟨c, hc⟩ := hnu.2.2 (mu k) (hmu.1 k)
  have : ∀ l, basisChange nu mu l k = c l := by
    intro l; simp only [basisChange]; rw [hc, coeff hnu]
  simp only [this]; exact hc

lemma bc_transpose (mu : K → Matrix I I ℂ) (nu : L → Matrix I I ℂ) :
    basisChange mu nu = (basisChange nu mu)ᵀ := by
  ext k l; simp only [basisChange, transpose_apply]; rw [Matrix.trace_mul_comm]

lemma orth {mu : K → Matrix I I ℂ} {nu : L → Matrix I I ℂ} (hmu : IsHermitianONBasis mu)
    (hnu : IsHermitianONBasis nu) : (basisChange nu mu)ᵀ * basisChange nu mu = 1 := by
  ext k k'
  have h := hmu.2.1 k k'
  rw [expand hmu hnu k', Matrix.mul_sum, Matrix.trace_sum] at h
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  simp only [Matrix.mul_apply, transpose_apply, Matrix.one_apply]
  rw [show (if k = k' then (1:ℝ) else 0) = ((if k = k' then 1 else 0 : ℂ)).re by split_ifs <;> simp,
    ← h2]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← tr_real (hmu.1 k) (hnu.1 l), ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [basisChange]; ring

lemma recon {mu : K → Matrix I I ℂ} {nu : L → Matrix I I ℂ} (hmu : IsHermitianONBasis mu)
    (hnu : IsHermitianONBasis nu) (c : K → ℝ) :
    hermitianReconstruction nu ((basisChange nu mu).mulVec c) = hermitianReconstruction mu c := by
  simp only [hermitianReconstruction, Matrix.mulVec, dotProduct]
  conv_rhs => arg 2; ext k; rw [expand hmu hnu k]
  simp only [Finset.smul_sum, smul_smul, Complex.ofReal_sum, Finset.sum_smul, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

/-- basis-free form of the pure-state equations. -/
lemma charac {mu : K → Matrix I I ℂ} (hmu : IsHermitianONBasis mu) (c : K → ℝ) :
    generalPureEquations mu c ↔
      (hermitianReconstruction mu c).trace.re = 1 ∧
      (hermitianReconstruction mu c * hermitianReconstruction mu c).trace.re = 1 ∧
      ∀ X : Matrix I I ℂ, X.IsHermitian →
        (hermitianReconstruction mu c * hermitianReconstruction mu c * X).trace.re =
          (hermitianReconstruction mu c * X).trace.re := by
  set ρ := hermitianReconstruction mu c
  have e1 : ρ.trace.re = ∑ a, c a * (mu a).trace.re := by
    simp [ρ, hermitianReconstruction, Matrix.trace_sum, Matrix.trace_smul]
  have e2 : (ρ * ρ).trace.re = dotProduct c c := by
    have : ∀ a, (ρ * mu a).trace.re = c a := fun a => coeff hmu c a
    simp only [ρ, hermitianReconstruction] at this ⊢
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.re_ofReal_mul, this]
  have e3 : ∀ g, (ρ * ρ * mu g).trace.re = ∑ a, ∑ b, c a * c b * (multiplicationCoefficient mu a b g).re := by
    intro g
    simp only [ρ, hermitianReconstruction, multiplicationCoefficient, Matrix.sum_mul, Matrix.mul_sum,
      Matrix.trace_sum, Complex.re_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    simp only [Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]; ring
  have e4 : ∀ g, (ρ * mu g).trace.re = c g := fun g => coeff hmu c g
  unfold generalPureEquations
  rw [← e1, ← e2]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h X hX => ?_, fun h g => ?_⟩)
  · obtain ⟨d, rfl⟩ := hmu.2.2 X hX
    simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, Complex.re_ofReal_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [e3, h g, e4]
  · rw [← e3, h (mu g) (hmu.1 g), e4]

end X4OB

-- ===== P35BSol =====

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

theorem _root_.solution (D : ℕ) (hD : 0 < D)
    (mu nu : Fin (D ^ 2) → Matrix (Fin D) (Fin D) ℂ)
    (hmu : IsHermitianONBasis mu) (hnu : IsHermitianONBasis nu) :
    let O := basisChange nu mu
    O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
    basisChange mu nu = O.transpose ∧
    (∀ c d : Fin (D ^ 2) → ℝ, dotProduct (O.mulVec c) (O.mulVec d) = dotProduct c d) ∧
    (∀ c : Fin (D ^ 2) → ℝ,
      hermitianReconstruction nu (O.mulVec c) = hermitianReconstruction mu c ∧
      O.transpose.mulVec (O.mulVec c) = c ∧
      (generalPureEquations mu c ↔ generalPureEquations nu (O.mulVec c))) ∧
    (∀ d : Fin (D ^ 2) → ℝ,
      O.mulVec (O.transpose.mulVec d) = d ∧
      (generalPureEquations nu d ↔ generalPureEquations mu (O.transpose.mulVec d))) := by
  intro O
  have h1 : O.transpose * O = 1 := X4OB.orth hmu hnu
  have ht : basisChange mu nu = O.transpose := X4OB.bc_transpose mu nu
  have h2 : O * O.transpose = 1 := by
    have := X4OB.orth hnu hmu
    rwa [ht, Matrix.transpose_transpose] at this
  refine ⟨h1, h2, ht, fun c d => ?_, fun c => ?_, fun d => ?_⟩
  · rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose,
      h1, Matrix.transpose_one, Matrix.one_mulVec]
  · have hr := X4OB.recon hmu hnu c
    refine ⟨hr, by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec], ?_⟩
    rw [X4OB.charac hmu, X4OB.charac hnu, hr]
  · have hr := X4OB.recon hnu hmu d
    rw [ht] at hr
    refine ⟨by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec], ?_⟩
    rw [X4OB.charac hmu, X4OB.charac hnu, hr]

end QAlgorithms.Papers.Independent.Support50.P35

end

#print axioms solution
