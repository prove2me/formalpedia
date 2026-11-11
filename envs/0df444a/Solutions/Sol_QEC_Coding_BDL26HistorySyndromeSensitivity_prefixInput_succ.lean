-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.prefixInput_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:29:00.06721+00:00
-- url     : https://prove2.me/submissions/b4b6f95f-0ed7-422e-882d-044a63e7e765

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
    (S : AlternatingStepData D) (n : Nat) (hn : n+1 ≤ depth)
    (sigma : D.family.Syndrome ⟨n+1,Nat.lt_succ_of_le hn⟩)
    (a : LevelIndex depth) (ha : a.val ≤ n) :
    prefixInput D S (n+1) hn sigma a (by omega) =
      prefixInput D S n (by omega) (S.step ⟨n,by omega⟩ sigma).coarse a ha := by
  have hne : ¬ a.val = n+1 := by omega
  rw [prefixInput]
  exact dif_neg hne
end QEC.Coding.BDL26HistorySyndromeSensitivity
