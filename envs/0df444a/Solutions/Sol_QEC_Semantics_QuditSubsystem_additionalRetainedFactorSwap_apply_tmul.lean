-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:15:34.346603+00:00
-- url     : https://prove2.me/submissions/76a54265-86ba-46e6-bcc3-080a651ad86a

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
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S T : QuditSubsystem q)
    (additional : S.additionalRetainedSystem T) (complement : T.complementSystem) :
    S.additionalRetainedFactorSwap T (additional ⊗ₜ[Complex] complement) =
      complement ⊗ₜ[Complex] additional :=
  rfl
end QEC.Semantics.QuditSubsystem
