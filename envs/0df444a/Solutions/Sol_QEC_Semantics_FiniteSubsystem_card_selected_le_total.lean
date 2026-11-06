-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.card_selected_le_total
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:51:38.156206+00:00
-- url     : https://prove2.me/submissions/e333c4c8-c4cc-42c4-839d-e4c27e4eb126

-- ID: b2b61c3f-3d40-433a-97b0-ae4198b4a459 | NAME: QEC.Semantics.FiniteSubsystem.card_selected_le_total | 未本地编译验证
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
    Fintype.card S.SelectedCoordinates ≤ Fintype.card ι := by
  exact Fintype.card_le_of_injective (fun x : S.SelectedCoordinates => (x : ι))
    (fun a b h => Subtype.ext h)
