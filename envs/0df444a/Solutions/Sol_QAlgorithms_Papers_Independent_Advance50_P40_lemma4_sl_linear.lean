-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P40.lemma4_sl_linear
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:20:38.395839+00:00
-- url     : https://prove2.me/submissions/bddb498b-fc4f-43f1-91f8-7a3d6af8934c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P40

lemma tr_add {α β : Type*} [Fintype β] (A B : Matrix (α × β) (α × β) ℂ) :
    QAlgorithms.traceRight (A + B) = QAlgorithms.traceRight A + QAlgorithms.traceRight B := by
  ext j k; simp [QAlgorithms.traceRight, Finset.sum_add_distrib]

lemma tr_smul {α β : Type*} [Fintype β] (c : ℂ) (A : Matrix (α × β) (α × β) ℂ) :
    QAlgorithms.traceRight (c • A) = c • QAlgorithms.traceRight A := by
  ext j k; simp [QAlgorithms.traceRight, Finset.mul_sum]

lemma src_add {n m : ℕ} (phi : BathFamily n m) (X Y : SystemMatrix n) :
    sourceAssignment phi (X + Y) = sourceAssignment phi X + sourceAssignment phi Y := by
  ext p q; simp [sourceAssignment, add_mul]

lemma src_smul {n m : ℕ} (phi : BathFamily n m) (c : ℂ) (X : SystemMatrix n) :
    sourceAssignment phi (c • X) = c • sourceAssignment phi X := by
  ext p q; simp [sourceAssignment, mul_assoc]

lemma qdp_add {n m : ℕ} (U : Matrix.unitaryGroup (Fin n × Fin m) ℂ) (A B : JointMatrix n m) :
    qdp U (A + B) = qdp U A + qdp U B := by
  unfold qdp; rw [mul_add, add_mul, tr_add]

lemma qdp_smul {n m : ℕ} (U : Matrix.unitaryGroup (Fin n × Fin m) ℂ) (c : ℂ) (A : JointMatrix n m) :
    qdp U (c • A) = c • qdp U A := by
  unfold qdp; rw [Matrix.mul_smul, Matrix.smul_mul, tr_smul]

lemma src_tr {n m : ℕ} (phi : BathFamily n m) (hphi : IsSLFamily phi) (R : SystemMatrix n) :
    sourceAssignment phi (QAlgorithms.traceRight (sourceAssignment phi R)) =
      sourceAssignment phi R := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [QAlgorithms.traceRight, sourceAssignment, Matrix.of_apply]
  rw [← Finset.mul_sum]
  rcases hphi.1 i j with h | h
  · simp [h]
  · have : ∑ c, phi i j c c = 1 := by rw [← h]; rfl
    rw [this, mul_one]

end QAlgorithms.Papers.Independent.Advance50.P40

end

open QAlgorithms.Papers.Independent.Advance50.P40 in
theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (phi : BathFamily n m) (hphi : IsSLFamily phi)
    (U : Matrix.unitaryGroup (Fin n × Fin m) ℂ) :
    ∃ F : SystemMatrix n →ₗ[ℂ] SystemMatrix n,
      (∀ X, F X = specifiedReducedMap phi U X) ∧
      ∀ R, IsSLAdmissibleInput phi R →
        F (QAlgorithms.traceRight (sourceAssignment phi R)) =
          qdp U (sourceAssignment phi R) := by
  refine ⟨{ toFun := specifiedReducedMap phi U
            map_add' := fun X Y => by simp only [specifiedReducedMap, src_add, qdp_add]
            map_smul' := fun c X => by simp only [specifiedReducedMap, src_smul, qdp_smul, RingHom.id_apply] },
    fun X => rfl, ?_⟩
  intro R _
  show specifiedReducedMap phi U _ = _
  simp only [specifiedReducedMap, src_tr phi hphi R]
