-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P17.sub_minEigenvalue_smul_one_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-30T10:44:06.631781+00:00
-- url     : https://prove2.me/submissions/fdad9206-1969-4397-afe3-96803e80df00

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section
open scoped Matrix ComplexOrder

namespace P17Aux

open Matrix

lemma cfcCont {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := by
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact Set.Finite.continuousOn (Set.finite_range hA.eigenvalues) f

lemma psdCfc {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (cfc f A).PosSemidef := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have hd : (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues : I → ℂ)).PosSemidef := by
    rw [posSemidef_diagonal_iff]; intro i
    simpa using hf i
  simpa [star_eq_conjTranspose] using hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix I I ℂ)

lemma traceCfc {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  rfl

lemma minEig_le {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (i : I) : QAlgorithms.minEigenvalue A ≤ hA.eigenvalues i := by
  have h : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  simp only [QAlgorithms.minEigenvalue, dif_pos h, QAlgorithms.ascEigenvalues, dif_pos hA,
    IsHermitian.eigenvalues]
  apply hA.eigenvalues₀_antitone
  rw [Fin.le_def]; simp; omega

theorem sme_main {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    (A - ((QAlgorithms.minEigenvalue A : ℝ) : ℂ) • (1 : Matrix I I ℂ)).PosSemidef := by
  have e : A - ((QAlgorithms.minEigenvalue A : ℝ) : ℂ) • (1 : Matrix I I ℂ) =
      cfc (fun x => x - QAlgorithms.minEigenvalue A) A := by
    rw [cfc_sub (hf := cfcCont hA _) (hg := cfcCont hA _), cfc_id' ℝ A, cfc_const _ A]
    simp [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
  rw [e]; exact psdCfc hA _ (fun i => sub_nonneg.mpr (minEig_le hA i))

end P17Aux

open QAlgorithms.Papers.Independent.Support50.P17 in
theorem solution {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    (A - ((QAlgorithms.minEigenvalue A : ℝ) : ℂ) • (1 : Matrix I I ℂ)).PosSemidef :=
  P17Aux.sme_main A hA

end
