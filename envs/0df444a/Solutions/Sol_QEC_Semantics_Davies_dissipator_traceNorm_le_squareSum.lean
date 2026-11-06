-- Prove2me | solution 1 for QEC.Semantics.Davies.dissipator_traceNorm_le_squareSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:12:34.6232+00:00
-- url     : https://prove2.me/submissions/c433b4bd-15b4-4805-8ef0-a1bcab881644

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
import Theorems.Thm_QEC_Semantics_Davies_traceNorm_sub_le
import Theorems.Thm_QEC_Semantics_Davies_gain_traceNorm_le
import Theorems.Thm_QEC_Semantics_Davies_dissipator_eq_gain_sub
import Theorems.Thm_QEC_Semantics_traceNorm_add_le
import Theorems.Thm_QEC_Semantics_traceNorm_mul_left_le
import Theorems.Thm_QEC_Semantics_traceNorm_mul_right_le
import Theorems.Thm_QEC_Semantics_traceNorm_smul


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
    traceNorm (lindbladDissipator J F) ≤ 2 * operatorNorm (squareSum J) * traceNorm F := by
  rw [dissipator_eq_gain_sub]
  apply (traceNorm_sub_le _ _).trans
  have hgain := gain_traceNorm_le J F hF
  have hloss : traceNorm ((2 : ℂ)⁻¹ • (squareSum J * F + F * squareSum J)) ≤
      operatorNorm (squareSum J) * traceNorm F := by
    rw [traceNorm_smul]
    have hsum := (traceNorm_add_le (squareSum J * F) (F * squareSum J)).trans
      (add_le_add (traceNorm_mul_left_le _ _) (traceNorm_mul_right_le _ _))
    norm_num at *
    linarith
  linarith
end QEC.Semantics.Davies
