-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.card_selected_add_card_complement
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:48:16.930205+00:00
-- url     : https://prove2.me/submissions/a480ec23-0b5f-480f-b509-a891cc5dda33

-- ID: deccff46-e6a4-4455-9d81-0e7753c28281 | NAME: QEC.Semantics.FiniteSubsystem.card_selected_add_card_complement | 未本地编译验证
import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution (S : FiniteSubsystem ι) :
    Fintype.card S.SelectedCoordinates + Fintype.card S.ComplementCoordinates =
      Fintype.card ι := by
  classical
  have hcompl : Fintype.card S.ComplementCoordinates =
      Fintype.card ι - Fintype.card S.SelectedCoordinates := by
    simpa [SelectedCoordinates, ComplementCoordinates] using
      (Fintype.card_subtype_compl (p := fun i : ι => i ∈ S.selected))
  have hle : Fintype.card S.SelectedCoordinates ≤ Fintype.card ι := by
    have hcard : Fintype.card S.SelectedCoordinates = S.selected.card := by
      simpa [SelectedCoordinates] using (Fintype.card_coe S.selected)
    rw [hcard]
    exact Finset.card_le_univ S.selected
  rw [hcompl]
  omega
