-- Prove2me | solution 1 for QEC.QLDPC.semanticQuditDistance_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:54:33.598589+00:00
-- url     : https://prove2.me/submissions/6f0e60f8-4b2b-4198-b466-5d1c2df61b43

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Theorems.Thm_QEC_QLDPC_semanticQuditDistance_attained
import Theorems.Thm_QEC_Semantics_QuditSubsystem_card_selected_le_total


set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v
namespace QEC.QLDPC
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q)) :
    semanticQuditDistance q code ≤ Fintype.card ι := by
  classical
  let weights : Set Nat := {weight | ∃ region : Semantics.QuditSubsystem q,
    Fintype.card region.SelectedCoordinates = weight ∧
      SupportsNondetectableLocalOperator code region}
  by_cases hnonempty : weights.Nonempty
  · obtain ⟨region, hcard, _⟩ := semanticQuditDistance_attained code hnonempty
    rw [← hcard]
    exact region.card_selected_le_total
  · have hempty : weights = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
    change sInf weights ≤ Fintype.card ι
    rw [hempty, Nat.sInf_empty]
    exact Nat.zero_le _
end QEC.QLDPC
