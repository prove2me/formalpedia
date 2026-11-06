-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.card_selected_le_total
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:48:08.750202+00:00
-- url     : https://prove2.me/submissions/d436c329-2412-4b61-aff8-4d691924c9e8

-- ID: 5100413d-8e94-4b9b-b936-4ec00190a61c | NAME: QEC.Semantics.QuditSubsystem.card_selected_le_total | 未本地编译验证
import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem solution (S : QuditSubsystem q) :
    Fintype.card S.SelectedCoordinates ≤ Fintype.card ι := by
  classical
  have hcard : Fintype.card S.SelectedCoordinates = S.selected.card := by
    simpa [SelectedCoordinates] using (Fintype.card_coe S.selected)
  rw [hcard]
  exact Finset.card_le_univ S.selected
