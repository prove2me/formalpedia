-- Prove2me | solution 1 for PI.QnHermHaar.tst_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:53.792945+00:00
-- url     : https://prove2.me/submissions/a815532b-a5c2-48fd-83eb-99276053b892

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorPreservesTest
import Theorems.Thm_PI_QnHermHaar_tst_H_zero
import Theorems.Thm_PI_QnHermHaar_tst_Z_fix
import Theorems.Thm_PI_QnHermHaar_tst_ZH_fix
import Theorems.Thm_PI_QnHermHaar_tst_core1
import Theorems.Thm_PI_QnHermHaar_tst_core2
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end Linfty
private theorem smul_mulVec_lemma {n : ℕ} (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext x
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end PI.QnHermHaar
end
end

set_option autoImplicit false
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.QnHermHaar
theorem _root_.solution {k r : ℕ} (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) ∧
    inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  have hH := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have hI := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hI
  have hfx : ∀ a' : Fin r, a'.val < i.val → ∀ p : Fin (2 * r + k + 1), (p = eI k r a' ∨ p = esI k r a') →
      Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) *ᵥ bvec p = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r) *ᵥ bvec p = 0 := by
    intro a' ha' p hp
    have hb : b.val < 2 * (r - i.val) + k + 1 := b.isLt
    have hi := i.isLt
    have hpb : (posL k r i b).val = b.val + i.val := rfl
    have hne : posL k r i b ≠ p := by
      intro e
      rcases hp with rfl | rfl
      · have := congrArg Fin.val e
        rw [hpb] at this
        have h2 : (eI k r a').val = a'.val := rfl
        omega
      · have := congrArg Fin.val e
        rw [hpb] at this
        have h2 : (esI k r a').val = 2 * r + k - a'.val := rfl
        omega
    have hz : Hpk k r (posL k r i a) p = 0 := by
      rcases hp with rfl | rfl
      · exact (tst_H_zero i a a' ha').1
      · exact (tst_H_zero i a a' ha').2
    exact ⟨tst_Z_fix _ _ _ hne, tst_ZH_fix _ _ _ _ _ hz⟩
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.conj_ofReal _
  have hs2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I, map_ofNat]
    ring
  constructor
  · refine ⟨?_, fun a' ha' => ⟨?_, ?_⟩⟩
    · simp only [hpart1, hinv]
      rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, tst_core1 _ _ hH hI,
        smul_zero]
    · obtain ⟨h1, h2⟩ := hfx a' ha' _ (Or.inl rfl)
      simp only [hpart1, hinv]
      rw [smul_mulVec_lemma, Matrix.sub_mulVec, h1, h2, sub_zero, smul_zero]
    · obtain ⟨h1, h2⟩ := hfx a' ha' _ (Or.inr rfl)
      simp only [hpart1, hinv]
      rw [smul_mulVec_lemma, Matrix.sub_mulVec, h1, h2, sub_zero, smul_zero]
  · refine ⟨?_, fun a' ha' => ⟨?_, ?_⟩⟩
    · simp only [hpart2, hinv]
      rw [Matrix.conjTranspose_smul, hs2, Matrix.smul_mul, Matrix.mul_smul, tst_core2 _ _ hH hI, neg_smul,
        neg_add_cancel]
    · obtain ⟨h1, h2⟩ := hfx a' ha' _ (Or.inl rfl)
      simp only [hpart2, hinv]
      rw [smul_mulVec_lemma, Matrix.add_mulVec, h1, h2, add_zero, smul_zero]
    · obtain ⟨h1, h2⟩ := hfx a' ha' _ (Or.inr rfl)
      simp only [hpart2, hinv]
      rw [smul_mulVec_lemma, Matrix.add_mulVec, h1, h2, add_zero, smul_zero]
end PI.QnHermHaar
