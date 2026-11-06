-- Prove2me | solution 1 for QEC.Semantics.Davies.gain_traceNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:10:34.138445+00:00
-- url     : https://prove2.me/submissions/444541ff-5f87-469c-9bb4-33e7e8a57027

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
import Theorems.Thm_QEC_Semantics_Davies_gain_traceNorm_le_positive
import Theorems.Thm_QEC_Semantics_Davies_traceNorm_sub_le
import Theorems.Thm_QEC_Semantics_negativePart_positive
import Theorems.Thm_QEC_Semantics_positivePart_positive
import Theorems.Thm_QEC_Semantics_positivePart_sub_negativePart
import Theorems.Thm_QEC_Semantics_traceNorm_eq_sum_parts


set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]
namespace QEC.Semantics.Davies
theorem _root_.solution (J : κ → Operator V) (F : Operator V)
    (hF : F.IsSymmetric) :
    traceNorm (lindbladJumpGain J F) ≤ operatorNorm (squareSum J) * traceNorm F := by
  calc
    traceNorm (lindbladJumpGain J F) =
        traceNorm (lindbladJumpGain J (positivePart F) -
          lindbladJumpGain J (negativePart F)) := by
      rw [← map_sub, positivePart_sub_negativePart F hF]
    _ ≤ traceNorm (lindbladJumpGain J (positivePart F)) +
        traceNorm (lindbladJumpGain J (negativePart F)) := traceNorm_sub_le _ _
    _ ≤ operatorNorm (squareSum J) * traceNorm (positivePart F) +
        operatorNorm (squareSum J) * traceNorm (negativePart F) :=
      add_le_add (gain_traceNorm_le_positive J _ (positivePart_positive F))
        (gain_traceNorm_le_positive J _ (negativePart_positive F))
    _ = operatorNorm (squareSum J) * traceNorm F := by
      rw [traceNorm_eq_sum_parts F hF, mul_add]
end QEC.Semantics.Davies
