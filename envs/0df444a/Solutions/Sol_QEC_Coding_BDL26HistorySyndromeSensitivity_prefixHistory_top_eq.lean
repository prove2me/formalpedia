-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.prefixHistory_top_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:00:19.368031+00:00
-- url     : https://prove2.me/submissions/6ed87150-7a9b-402f-98a3-d066808e8cb4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_buildCorrectionHistory_eq_of_recursion
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
universe u
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D) (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    prefixHistory D S B depth (Nat.le_refl _) sigma = buildCorrectionHistory D S B sigma := by
  symm
  apply buildCorrectionHistory_eq_of_recursion D S B (prefixHistory D S B)
  · intro hn s
    rw [prefixHistory] <;> rfl
  · intro n hn s
    rw [prefixHistory] <;> rfl
end QEC.Coding.BDL26HistorySyndromeSensitivity
