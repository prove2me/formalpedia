-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.linearUp_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:48:11.458771+00:00
-- url     : https://prove2.me/submissions/f0558cb2-36e8-4da6-827d-5ccf8c18ae81

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals

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
    (b : Nat) (hb : b ≤ depth) :
    linearUp edge b hb ⟨b,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _) = LinearMap.id := by
  cases b with
  | zero => rw [linearUp] <;> rfl
  | succ b =>
      rw [linearUp]
      exact dif_pos rfl
end QEC.Coding.BDL26HistoryErrorTelescoping
