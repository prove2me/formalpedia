-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.linearUp_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:45:16.219235+00:00
-- url     : https://prove2.me/submissions/4ae6c36c-a1f0-4158-b859-e85db5945039

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder
open scoped Classical
universe u v
variable {depth : Nat} {V : LevelIndex depth → Type u}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module BDL26Field (V i)]
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution
    (edge : ∀ i : StepIndex depth, V i.castSucc →ₗ[BDL26Field] V i.succ)
    (b : Nat) (hb : b+1 ≤ depth) (a : LevelIndex depth) (ha : a.val ≤ b) :
    linearUp edge (b+1) hb a (ha.trans (Nat.le_succ b)) =
      (edge ⟨b,by omega⟩).comp (linearUp edge b (by omega) a ha) := by
  have hne : ¬ a.val = b+1 := by omega
  rw [linearUp]
  exact dif_neg hne
end QEC.Coding.BDL26HistoryErrorTelescoping
