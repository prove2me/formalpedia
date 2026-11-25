-- Prove2me | solution 1 for PI.QnHermHaar.tst_ZH_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:19:12.101354+00:00
-- url     : https://prove2.me/submissions/c838e04d-0536-40af-8509-b5254f6c498b

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
theorem _root_.solution {n : ℕ} (W H : Matrix (Fin n) (Fin n) ℂ) (a' b' p : Fin n) (h : H a' p = 0) :
    (W * (Matrix.single a' b' (1 : ℂ))ᴴ * H) *ᵥ bvec p = 0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h0 : (Matrix.single a' b' (1 : ℂ))ᴴ *ᵥ (H *ᵥ bvec p) = 0 := by
    ext x
    simp [bvec, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.single_apply, Pi.single_apply, h]
    by_cases hb : b' = x <;> simp [hb, h]
  rw [h0, Matrix.mulVec_zero]
end PI.QnHermHaar
