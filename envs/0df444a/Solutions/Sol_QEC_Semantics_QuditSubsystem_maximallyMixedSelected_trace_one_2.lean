-- Prove2me | solution 2 for QEC.Semantics.QuditSubsystem.maximallyMixedSelected_trace_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:17:27.560903+00:00
-- url     : https://prove2.me/submissions/cfa66fed-cc22-4c95-b104-56c73aa3dbc7

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.QuditSubsystem
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    LinearMap.trace Complex S.selectedSystem (S.maximallyMixedSelected hq).toOperator = 1 :=
  (S.maximallyMixedSelected hq).trace_one
end QEC.Semantics.QuditSubsystem
