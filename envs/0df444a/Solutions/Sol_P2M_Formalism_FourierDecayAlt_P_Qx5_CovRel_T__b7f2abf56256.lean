-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Qx5_CovRel_T__b7f2abf56256
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:08.373058+00:00
-- url     : https://prove2.me/submissions/bbc12adf-dff5-4593-86ac-eb04dfd80f97

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
variable {E : Fin n → Fin n → A} {η : Fin n → A} {x : Fin n → ℂ} {ζ : A}
namespace Formalism.FourierDecayAlt.P.Qx5
namespace CovRel
theorem _root_.solution (h : CovRel E η x ζ) (w : ℂ) (a b : Fin n) :
    Tm E w a b * ζ = ζ * Tm E w a b + x b • η a := by
  have h1 := h.Eζ a b
  have h2 : E a b * ζ = ζ * E a b + x b • η a := by rw [← h1]; abel
  unfold Tm
  rw [add_mul, mul_add, h2]
  split_ifs
  · rw [Algebra.commutes]; abel
  · simp
end CovRel
end Formalism.FourierDecayAlt.P.Qx5
