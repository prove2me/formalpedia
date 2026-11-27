-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.upper_block_det_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:18.051426+00:00
-- url     : https://prove2.me/submissions/f4e4bb18-33f6-4738-9dc6-ce95e929d991

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ParabolicBlockForms_UpperBlockRankOneUpdate
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_C4_Bq_NQ_upper_block_rank_one_update

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq
open Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
variable {n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.Act.C4.Bq
namespace NQ
theorem _root_.solution {i₀ : Fin n} {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hM : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    M.toBlocks₁₁.det = 1 := by
  rw [hM.upper_block_rank_one_update, det_one_add_replicateCol_mul_replicateRow]
  have h0 : (M - 1) (Sum.inl i₀) (Sum.inl i₀) = 0 := hM.1 _
  rw [Matrix.sub_apply, sub_eq_zero] at h0
  simp [dotProduct, Pi.single_apply, h0]
end NQ
end PositivityTheory.SiegelWeilFormula.Act.C4.Bq
