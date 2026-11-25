-- Prove2me | solution 1 for PI.QnHermHaar.tst_exp_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:19.361923+00:00
-- url     : https://prove2.me/submissions/1a8fc6d2-4e17-419f-a0e0-265cc732abad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorPreservesTest
import Theorems.Thm_PI_QnHermHaar_tst_exp_hasSum
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
namespace PI.QnHermHaar
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hv : X *ᵥ v = 0) :
    NormedSpace.exp X *ᵥ v = v := by
  have hc : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => M *ᵥ v :=
    Continuous.matrix_mulVec continuous_id continuous_const
  have h1 := (tst_exp_hasSum X).map (AddMonoidHom.mk' (fun M : Matrix (Fin n) (Fin n) ℂ => M *ᵥ v)
    (fun A B => Matrix.add_mulVec A B v)) hc
  have h2 : HasSum (fun j : ℕ => ((j.factorial : ℂ)⁻¹ • X ^ j) *ᵥ v) v := by
    have h := hasSum_single (f := fun j : ℕ => ((j.factorial : ℂ)⁻¹ • X ^ j) *ᵥ v) 0 (by
      intro j hj
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      show ((((m + 1).factorial : ℕ) : ℂ)⁻¹ • X ^ (m + 1)) *ᵥ v = 0
      rw [smul_mulVec_lemma, pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, smul_zero])
    simpa using h
  exact h1.unique h2
end PI.QnHermHaar
