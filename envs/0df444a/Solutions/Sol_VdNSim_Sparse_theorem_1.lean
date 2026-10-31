-- Prove2me | solution 1 for VdNSim.Sparse.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T21:50:22.346464+00:00
-- url     : https://prove2.me/submissions/c83feaf3-5d68-475a-98d5-adade634b224

import Theorems.Thm_VdNSim_Sparse_theorem_3

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace AuxThm1
open VdNSim.Sparse

lemma matElem_eq_dotProduct {X : Type*} [Fintype X]
    (ϕ : X → ℂ) (A : Matrix X X ℂ) (ψ : X → ℂ) :
    matElem ϕ A ψ = star ϕ ⬝ᵥ (A *ᵥ ψ) := by
  unfold matElem dotProduct Matrix.mulVec
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp only [Pi.star_apply, dotProduct, Finset.mul_sum, mul_assoc]

lemma matElem_mulVec {X : Type*} [Fintype X]
    (U O : Matrix X X ℂ) (ψ : X → ℂ) :
    matElem (U *ᵥ ψ) O (U *ᵥ ψ) = matElem ψ (Uᴴ * O * U) ψ := by
  rw [matElem_eq_dotProduct, matElem_eq_dotProduct]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

lemma clm_mul_apply {n : ℕ} (A B : Matrix (Bits n) (Bits n) ℂ)
    (v : EuclideanSpace ℂ (Bits n)) :
    Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) (A * B) v =
      Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) A
        (Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) B v) := by
  change QAlgorithms.act (A * B) v = QAlgorithms.act A (QAlgorithms.act B v)
  unfold QAlgorithms.act
  simp [Matrix.mulVec_mulVec]

lemma clm_norm_of_unitary {n : ℕ} {V : Matrix (Bits n) (Bits n) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Bits n) ℂ) (v : EuclideanSpace ℂ (Bits n)) :
    ‖Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) V v‖ = ‖v‖ :=
  QAlgorithms.act_norm_of_mem_unitaryGroup hV v

lemma specNorm_conj_le_one {n : ℕ}
    (U : Matrix.unitaryGroup (Bits n) ℂ)
    (O : Matrix (Bits n) (Bits n) ℂ)
    (hO1 : QAlgorithms.specNorm O ≤ 1) :
    QAlgorithms.specNorm (Matrix.conjTranspose (U : Matrix (Bits n) (Bits n) ℂ) * O *
      (U : Matrix (Bits n) (Bits n) ℂ)) ≤ 1 := by
  change ‖Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ)
    (Matrix.conjTranspose (U : Matrix (Bits n) (Bits n) ℂ) * O *
      (U : Matrix (Bits n) (Bits n) ℂ))‖ ≤ 1
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  have hU : (U : Matrix (Bits n) (Bits n) ℂ) ∈ Matrix.unitaryGroup (Bits n) ℂ := U.2
  have hUstar : Matrix.conjTranspose (U : Matrix (Bits n) (Bits n) ℂ) ∈
      Matrix.unitaryGroup (Bits n) ℂ := (U⁻¹).2
  rw [clm_mul_apply, clm_mul_apply, clm_norm_of_unitary hUstar]
  have hle := ContinuousLinearMap.le_opNorm
    (Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) O)
    (Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) (U : Matrix (Bits n) (Bits n) ℂ) v)
  rw [clm_norm_of_unitary hU] at hle
  have hO1' : ‖Matrix.toEuclideanCLM (n := Bits n) (𝕜 := ℂ) O‖ ≤ 1 := hO1
  exact hle.trans (mul_le_mul_of_nonneg_right hO1' (norm_nonneg v))

end AuxThm1

open VdNSim.Sparse AuxThm1 in
theorem solution {n s K : ℕ} (hK : 0 < K)
    (ψ : Bits n → ℂ) (hψ : ∑ x, prob ψ x = 1)
    (U : Matrix.unitaryGroup (Bits n) ℂ)
    (O : Matrix (Bits n) (Bits n) ℂ)
    (hO : O.IsHermitian) (hO1 : QAlgorithms.specNorm O ≤ 1)
    (hsp : IsSparse s (Matrix.conjTranspose (U : Matrix (Bits n) (Bits n) ℂ) * O *
      (U : Matrix (Bits n) (Bits n) ℂ)))
    (D : ColumnData (Matrix.conjTranspose (U : Matrix (Bits n) (Bits n) ℂ) * O *
      (U : Matrix (Bits n) (Bits n) ℂ)) s)
    {ε : ℝ} (hε : 0 < ε) :
    failProb ψ ψ D K
      (matElem ((U : Matrix (Bits n) (Bits n) ℂ) *ᵥ ψ) O
        ((U : Matrix (Bits n) (Bits n) ℂ) *ᵥ ψ)) ε ≤
      8 * (s : ℝ) * Real.exp (-((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4)) := by
  have _ := hO
  rw [matElem_mulVec (U : Matrix (Bits n) (Bits n) ℂ) O ψ]
  exact theorem_3 hK ψ ψ hψ hψ
    (Matrix.conjTranspose (U : Matrix (Bits n) (Bits n) ℂ) * O *
      (U : Matrix (Bits n) (Bits n) ℂ))
    hsp (specNorm_conj_le_one U O hO1) D hε
