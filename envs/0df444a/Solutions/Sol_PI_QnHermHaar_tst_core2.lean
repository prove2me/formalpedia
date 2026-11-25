-- Prove2me | solution 1 for PI.QnHermHaar.tst_core2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:16:13.099205+00:00
-- url     : https://prove2.me/submissions/edd430cc-d59e-4686-a5db-6f6d615a7dee

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorPreservesTest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.QnHermHaar
theorem _root_.solution {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hH2 : H * H = 1) :
    (Z + H * Zᴴ * H)ᴴ * H = H * (Z + H * Zᴴ * H) := by
  have hHH : ∀ Y : Matrix (Fin n) (Fin n) ℂ, H * (H * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hH2, Matrix.one_mul]
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hH2, hHH, Matrix.mul_one]
  abel
end PI.QnHermHaar
