-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.lazySubspace_stabilizingHamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:59:04.572389+00:00
-- url     : https://prove2.me/submissions/3245b049-ffc0-43e0-bd8a-ca00c5f17c9e

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

lemma X7SH_act_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    QAlgorithms.act A (QAlgorithms.act B v) = QAlgorithms.act (A * B) v := by
  simp [QAlgorithms.act, Matrix.mulVec_mulVec]

lemma X7SH_act_inj {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ v, QAlgorithms.act A v = QAlgorithms.act B v) : A = B := by
  have : Matrix.toEuclideanLin A = Matrix.toEuclideanLin B := LinearMap.ext h
  exact Matrix.toEuclideanLin.injective this

lemma X7SH_projAct {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : EuclideanSpace ℂ (Fin n)) :
    QAlgorithms.act (orthogonalProjector S) v = S.starProjection v := by
  have hv : v = ∑ j, v j • (WithLp.toLp 2 (fun k => if k = j then (1 : ℂ) else 0) :
      EuclideanSpace ℂ (Fin n)) := by
    ext i
    simp [Finset.sum_apply]
  conv_rhs => rw [hv]
  rw [map_sum]
  ext i
  simp only [map_smul, QAlgorithms.act, Matrix.mulVec, dotProduct, orthogonalProjector]
  simp [Finset.sum_apply, mul_comm]


lemma X7SH_proj_entry {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (i j : Fin n) :
    orthogonalProjector S i j =
      inner ℂ (EuclideanSpace.single i (1 : ℂ)) (S.starProjection (EuclideanSpace.single j (1 : ℂ))) := by
  rw [EuclideanSpace.inner_single_left]
  have : (WithLp.toLp 2 (fun k => if k = j then (1 : ℂ) else 0) : EuclideanSpace ℂ (Fin n)) =
      EuclideanSpace.single j (1 : ℂ) := by
    ext k; simp
  simp [orthogonalProjector, this]

lemma X7SH_proj_herm {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    (orthogonalProjector S)ᴴ = orthogonalProjector S := by
  ext i j
  rw [Matrix.conjTranspose_apply, X7SH_proj_entry, X7SH_proj_entry,
    ← Submodule.inner_starProjection_left_eq_right, ← inner_conj_symm]
  simp

lemma X7SH_proj_idem {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    orthogonalProjector S * orthogonalProjector S = orthogonalProjector S := by
  apply X7SH_act_inj
  intro v
  rw [← X7SH_act_mul, X7SH_projAct, X7SH_projAct]
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

lemma X7SH_adjoin_inv {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : invariant G S) :
    invariant (Algebra.adjoin ℂ G : Set (Matrix (Fin n) (Fin n) ℂ)) S := by
  intro X hX
  induction hX using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap c =>
    intro v hv
    have : QAlgorithms.act (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) c) v = c • v := by
      ext i; simp [QAlgorithms.act, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    rw [this]; exact S.smul_mem c hv
  | add x y _ _ hx hy =>
    intro v hv
    have : QAlgorithms.act (x + y) v = QAlgorithms.act x v + QAlgorithms.act y v := by
      ext i; simp [QAlgorithms.act, Matrix.add_mulVec]
    rw [this]; exact S.add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy =>
    intro v hv
    rw [← X7SH_act_mul]; exact hx _ (hy v hv)

/-- If (1-P) K P = 0 then S is K-invariant. -/
lemma X7SH_block_inv {n : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (K : Matrix (Fin n) (Fin n) ℂ)
    (hK : (1 - orthogonalProjector S) * K * orthogonalProjector S = 0) :
    ∀ v ∈ S, QAlgorithms.act K v ∈ S := by
  intro v hv
  have hPv : QAlgorithms.act (orthogonalProjector S) v = v := by
    rw [X7SH_projAct]; exact Submodule.starProjection_eq_self_iff.mpr hv
  have e : K * orthogonalProjector S = orthogonalProjector S * (K * orthogonalProjector S) := by
    have := hK
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    rw [← Matrix.mul_assoc, ← this]
  rw [← hPv, X7SH_act_mul, e, ← X7SH_act_mul, X7SH_projAct]
  exact Submodule.starProjection_apply_mem _ _


lemma X7SH_block {n : ℕ} (D : LindbladData n) (S : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hb : stabilizingBlock D S H) :
    (1 - orthogonalProjector S) * driftK (controlledData D H hH) * orthogonalProjector S = 0 := by
  unfold stabilizingBlock at hb
  set P := orthogonalProjector S
  set M := ∑ k, (D.jump k)ᴴ * D.jump k
  have hd : driftK (controlledData D H hH) = Complex.I • (D.drift + H) + (1 / 2 : ℂ) • M := rfl
  rw [hd]
  have e1 : (1 - P) * (Complex.I • (D.drift + H) + (1 / 2 : ℂ) • M) * P =
      Complex.I • ((1 - P) * D.drift * P) + Complex.I • ((1 - P) * H * P) +
        (1 / 2 : ℂ) • ((1 - P) * M * P) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add]
  have e2 : (1 - P) * H * P = -((1 - P) * D.drift * P) - (1 / (2 * Complex.I)) • ((1 - P) * M * P) := by
    rw [hb]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
    abel
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  rw [e1, e2, smul_sub, smul_neg, smul_smul, hI]
  abel

end QAlgorithms.Papers.Independent.Dependency50.P16

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Dependency50.P16 in
theorem solution {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (S : Submodule ℂ ((fun n : ℕ => EuclideanSpace ℂ (Fin n)) n)) (hS : lazy D.jump S) :
    (∃ (H : (fun n : ℕ => Matrix (Fin n) (Fin n) ℂ) n) (hH : H.IsHermitian), stabilizingBlock D S H ∧
      collecting (driftK (controlledData D H hH)) D.jump S) ∧
    (∀ (H : (fun n : ℕ => Matrix (Fin n) (Fin n) ℂ) n) (hH : H.IsHermitian), stabilizingBlock D S H →
      collecting (driftK (controlledData D H hH)) D.jump S) := by
  have hall : ∀ (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), stabilizingBlock D S H →
      collecting (driftK (controlledData D H hH)) D.jump S := by
    intro H hH hb
    refine ⟨hS.1, X7SH_adjoin_inv _ S ?_⟩
    intro X hX
    rcases hX with rfl | hX
    · exact X7SH_block_inv S _ (X7SH_block D S H hH hb)
    · exact hS.2 X hX
  refine ⟨?_, hall⟩
  set P := orthogonalProjector S with hPdef
  set X := D.drift + (1 / (2 * Complex.I)) • ∑ k, (D.jump k)ᴴ * D.jump k
  set Y := (1 - P) * X * P
  have hPP : P * P = P := X7SH_proj_idem S
  have hPh : Pᴴ = P := X7SH_proj_herm S
  have hQP : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, sub_zero]
  have hQh : (1 - P)ᴴ = 1 - P := by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh]
  have hH : (-(Y + Yᴴ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  refine ⟨-(Y + Yᴴ), hH, ?_, hall _ hH ?_⟩ <;>
  · unfold stabilizingBlock
    rw [← hPdef]
    have hYh : Yᴴ = P * Xᴴ * (1 - P) := by
      simp only [Y, Matrix.conjTranspose_mul, hPh, hQh, Matrix.mul_assoc]
    have t1 : (1 - P) * Y * P = (1 - P) * X * P := by
      calc (1 - P) * Y * P = ((1 - P) * (1 - P)) * X * (P * P) := by
            simp only [Y, Matrix.mul_assoc]
        _ = _ := by rw [hQQ, hPP]
    have t2 : (1 - P) * Yᴴ * P = 0 := by
      calc (1 - P) * Yᴴ * P = ((1 - P) * P) * (Xᴴ * (1 - P) * P) := by
            simp only [hYh, Matrix.mul_assoc]
        _ = 0 := by rw [hQP, Matrix.zero_mul]
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_add, Matrix.add_mul, t1, t2, add_zero,
      Matrix.neg_mul, Matrix.neg_mul]
