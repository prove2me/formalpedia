-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.sum_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:49:45.425693+00:00
-- url     : https://prove2.me/submissions/72e93069-7483-40f3-aa46-b3981d01f279

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumEqSumCompEmbedding
import Definitions.Def_Lemmata_B110_ExistsMoved
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Theorems.Thm_GlobalTheory_EmbeddingSum_sum_eq_sum_comp_embedding


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
variable {N j : ℕ}
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution (e : Fin j ↪ Fin N) (f : Fin N → ℂ) (hf : ∀ c, c ∉ Set.range e → f c = 0) :
    ∑ c, f c = ∑ a, f (e a) := by
  first | exact GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding .. | (apply GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding <;> assumption) | (intros; apply GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding <;> assumption) | (apply @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding <;> assumption) | (intros; apply @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding <;> assumption) | (apply @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding <;> first | assumption | infer_instance) | exact @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding N j e f hf | exact @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding N j e f | exact @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding N j e | exact @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding N j | exact @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding N
end PI.UnitaryCorollaryDerivatives.DjC
