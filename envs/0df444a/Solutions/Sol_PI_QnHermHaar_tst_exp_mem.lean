-- Prove2me | solution 1 for PI.QnHermHaar.tst_exp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:43.195485+00:00
-- url     : https://prove2.me/submissions/3b6e6408-fc3a-4ecb-8b0b-b51f7fc02941

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorPreservesTest
import Theorems.Thm_PI_QnHermHaar_tst_exp_mulVec
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
theorem _root_.solution {k r : ℕ} {i : Fin (r + 1)} {X : Mx k r} (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  obtain ⟨hLie, hfix⟩ := hX
  have hI := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hunitH : IsUnit (Hpk k r) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hI)
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hI
  have hst : star ((t : ℂ)) = (t : ℂ) := Complex.conj_ofReal t
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · have hXc : Xᴴ = Hpk k r * (-X) * Hpk k r := by
      have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hLie
      calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, hI, Matrix.mul_one]
        _ = Hpk k r * (-X) * Hpk k r := by rw [h1, Matrix.mul_neg]
    have hYc : ((t : ℂ) • X)ᴴ = Hpk k r * (-((t : ℂ) • X)) * (Hpk k r)⁻¹ := by
      rw [hinv, Matrix.conjTranspose_smul, hst, hXc, ← smul_neg, Matrix.mul_smul, Matrix.smul_mul]
    have hE : (NormedSpace.exp ((t : ℂ) • X))ᴴ =
        Hpk k r * NormedSpace.exp (-((t : ℂ) • X)) * (Hpk k r)⁻¹ := by
      rw [← Matrix.exp_conjTranspose, hYc, Matrix.exp_conj _ _ hunitH]
    have hEE : NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
      rw [Matrix.exp_neg]
      exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))
    show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • X) = Hpk k r
    rw [hE, hinv, Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-((t : ℂ) • X))) (Hpk k r) (Hpk k r), hI,
      Matrix.mul_one, Matrix.mul_assoc, hEE, Matrix.mul_one]
  · exact tst_exp_mulVec _ _ (by rw [smul_mulVec_lemma, (hfix a ha).1, smul_zero])
  · exact tst_exp_mulVec _ _ (by rw [smul_mulVec_lemma, (hfix a ha).2, smul_zero])
end PI.QnHermHaar
