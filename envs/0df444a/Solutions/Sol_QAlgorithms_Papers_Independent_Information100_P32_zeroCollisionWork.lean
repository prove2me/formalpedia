-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.zeroCollisionWork
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:21:48.164218+00:00
-- url     : https://prove2.me/submissions/4930fa34-be8e-4c77-ab86-ade1a9e74d35

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

theorem X7_commute_free_int (w j : ℝ) :
    Commute (freeEnergy w) (interaction j) := by
  unfold Commute SemiconjBy
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [freeEnergy, interaction, localEnergy, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.kronecker, Matrix.kroneckerMap_apply, QAlgorithms.pauliX, QAlgorithms.pauliY,
      QAlgorithms.pauliZ, Matrix.one_apply] <;> ring

theorem X7_herm (w j : ℝ) :
    (freeEnergy w + interaction j)ᴴ = freeEnergy w + interaction j := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [freeEnergy, interaction, localEnergy, Fintype.sum_prod_type,
      Matrix.kronecker, Matrix.kroneckerMap_apply, QAlgorithms.pauliX, QAlgorithms.pauliY,
      QAlgorithms.pauliZ, Matrix.one_apply, Complex.ext_iff]

theorem X7_unitary (h : Op (Bool × Bool)) (hh : hᴴ = h) (t : ℝ) :
    (evolution h t)ᴴ * evolution h t = 1 := by
  unfold evolution
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hh]
  have : star (-(t : ℂ) * Complex.I) = -(-(t : ℂ) * Complex.I) := by
    simp [Complex.ext_iff]
  rw [this, neg_smul]
  set X : Op (Bool × Bool) := (-(t : ℂ) * Complex.I) • h
  rw [← Matrix.exp_add_of_commute (-X) X (Commute.neg_left (Commute.refl X)),
    neg_add_cancel, NormedSpace.exp_zero]

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution (m : Model) (r : Op Bool) (hr : IsDensityMatrix r) :
    Commute (interaction m.coupling)
      (evolution (freeEnergy m.frequency + interaction m.coupling) m.duration) ∧ work m r = 0 := by
  have hc : Commute (interaction m.coupling)
      (evolution (freeEnergy m.frequency + interaction m.coupling) m.duration) := by
    unfold evolution
    apply Commute.exp_right
    apply Commute.smul_right
    exact ((X7_commute_free_int _ _).symm).add_right (Commute.refl _)
  refine ⟨hc, ?_⟩
  unfold work observableChange
  simp only
  rw [Matrix.mul_assoc, hc.eq, ← Matrix.mul_assoc,
    X7_unitary _ (X7_herm _ _), Matrix.one_mul, sub_self, Matrix.zero_mul,
    Matrix.trace_zero, Complex.zero_re]

end
