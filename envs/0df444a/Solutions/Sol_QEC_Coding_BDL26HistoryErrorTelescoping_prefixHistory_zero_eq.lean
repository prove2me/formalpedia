-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.prefixHistory_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:35:05.217792+00:00
-- url     : https://prove2.me/submissions/31dbda40-8acf-4419-a1cf-600ee27cb040

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (D : BDL26DecoderData depth C0 C1 C2)
    (st : AlternatingStepData D) (B : AuditedBaseDecoder D) (s : D.family.Syndrome 0) :
    prefixHistory D st B 0 (Nat.zero_le _) s =
      [.base {
        input := s
        correction := B.decode s
        relation := (B.rightInverse s).symm }] := by
  have hz (hn : 0 ≤ depth)
      (t : D.family.Syndrome ⟨0,Nat.lt_succ_of_le hn⟩) :
      prefixHistory D st B 0 hn t = [.base {
        input := t
        correction := B.decode t
        relation := (B.rightInverse t).symm }] := by
    rw [prefixHistory] <;> rfl
  exact hz (Nat.zero_le _) s
end QEC.Coding.BDL26HistoryErrorTelescoping
