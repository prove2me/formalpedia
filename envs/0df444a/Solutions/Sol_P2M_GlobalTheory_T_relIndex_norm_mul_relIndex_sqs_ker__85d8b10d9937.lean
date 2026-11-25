-- Prove2me | solution 1 for P2M_GlobalTheory_T_relIndex_norm_mul_relIndex_sqs_ker__85d8b10d9937
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:00.430599+00:00
-- url     : https://prove2.me/submissions/0173a856-d225-4040-99c2-d9c04179cb84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexNormMulRelIndexSqsKer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexNormMulRelIndexSqsKerStatement
import Theorems.Thm_GlobalTheory_QNorm_relIndex_norm_mul_relIndex_sqs_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommGroup A] (σ : A →* A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) * (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) := by
  first | exact @GlobalTheory.QNorm.relIndex_norm_mul_relIndex_sqs_ker | exact GlobalTheory.QNorm.relIndex_norm_mul_relIndex_sqs_ker | (intros; apply GlobalTheory.QNorm.relIndex_norm_mul_relIndex_sqs_ker <;> assumption)
end _root_.GlobalTheory.T
