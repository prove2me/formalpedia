-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Qx5_CovRel_T__b923ad0ccb28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:02.04846+00:00
-- url     : https://prove2.me/submissions/4cc281be-fa26-4701-9a68-a4924fdba939

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
theorem _root_.solution (h : CovRel E η x ζ) (w : ℂ) (a b c : Fin n) :
    Tm E w a b * η c = η c * Tm E (w - 1) a b + (if a = b then η c else 0) + (if b = c then η a else 0) := by
  have h1 := h.Eη a b c
  have h2 : E a b * η c = η c * E a b + (if b = c then η a else 0) := by rw [← h1]; abel
  unfold Tm
  rw [add_mul, mul_add, h2]
  by_cases hab : a = b
  · simp only [hab, if_true]
    rw [Algebra.commutes, map_sub, map_one, mul_sub, mul_one]
    abel
  · simp [hab]
end CovRel
end Formalism.FourierDecayAlt.P.Qx5
