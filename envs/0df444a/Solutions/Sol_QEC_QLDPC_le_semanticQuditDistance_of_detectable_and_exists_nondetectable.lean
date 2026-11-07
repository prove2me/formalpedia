-- Prove2me | solution 1 for QEC.QLDPC.le_semanticQuditDistance_of_detectable_and_exists_nondetectable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:54:35.808203+00:00
-- url     : https://prove2.me/submissions/ac937ccb-3fb9-4331-ac44-5a835807516d

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Theorems.Thm_QEC_QLDPC_semanticQuditDistance_attained

set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v
namespace QEC.QLDPC
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (d : Nat)
    (hdetect : ∀ region : Semantics.QuditSubsystem q,
      Fintype.card region.SelectedCoordinates < d →
        ∀ localOperator : Semantics.Operator region.selectedSystem,
          Semantics.DetectableOn code
            (region.extendLocalToRegister localOperator))
    (hexists : ∃ region : Semantics.QuditSubsystem q,
      SupportsNondetectableLocalOperator code region) :
    d ≤ semanticQuditDistance q code := by
  have hnonempty : {weight : Nat | ∃ region : Semantics.QuditSubsystem q,
      Fintype.card region.SelectedCoordinates = weight ∧
        SupportsNondetectableLocalOperator code region}.Nonempty := by
    obtain ⟨region, hregion⟩ := hexists
    exact ⟨Fintype.card region.SelectedCoordinates, region, rfl, hregion⟩
  obtain ⟨region, hcard, localOperator, hnot⟩ :=
    semanticQuditDistance_attained code hnonempty
  by_contra hless
  exact hnot (hdetect region (by omega) localOperator)
end QEC.QLDPC
