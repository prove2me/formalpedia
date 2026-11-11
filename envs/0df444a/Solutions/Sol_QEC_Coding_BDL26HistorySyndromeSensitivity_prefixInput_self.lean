-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.prefixInput_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:24:33.702813+00:00
-- url     : https://prove2.me/submissions/7cef36e0-623f-4c46-94dc-af90642a66ab

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots

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
    (S : AlternatingStepData D) (n : Nat) (hn : n ≤ depth)
    (sigma : D.family.Syndrome ⟨n,Nat.lt_succ_of_le hn⟩) :
    prefixInput D S n hn sigma ⟨n,Nat.lt_succ_of_le hn⟩ (Nat.le_refl _) = sigma := by
  cases n with
  | zero => rw [prefixInput] <;> rfl
  | succ n =>
      rw [prefixInput]
      exact dif_pos rfl
end QEC.Coding.BDL26HistorySyndromeSensitivity
