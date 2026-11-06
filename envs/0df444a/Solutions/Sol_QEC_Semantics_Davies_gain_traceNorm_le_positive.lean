-- Prove2me | solution 1 for QEC.Semantics.Davies.gain_traceNorm_le_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:08:35.331936+00:00
-- url     : https://prove2.me/submissions/5ea026a1-525a-461c-9604-82b75fe97b92

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
import Theorems.Thm_QEC_Semantics_Davies_gain_positive
import Theorems.Thm_QEC_Semantics_Davies_trace_gain
import Theorems.Thm_QEC_Semantics_norm_trace_le_traceNorm
import Theorems.Thm_QEC_Semantics_traceNorm_eq_re_trace_of_positive
import Theorems.Thm_QEC_Semantics_traceNorm_mul_left_le


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
    (hF : F.IsPositive) :
    traceNorm (lindbladJumpGain J F) ≤ operatorNorm (squareSum J) * traceNorm F := by
  rw [traceNorm_eq_re_trace_of_positive _ (gain_positive J F hF), trace_gain]
  exact (Complex.re_le_norm _).trans ((norm_trace_le_traceNorm _).trans
    (traceNorm_mul_left_le _ _))
end QEC.Semantics.Davies
