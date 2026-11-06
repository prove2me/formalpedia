-- Prove2me | solution 2 for QEC.Semantics.QuditSubsystem.recombine_splitLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:01:32.627197+00:00
-- url     : https://prove2.me/submissions/3b17a370-fb92-428e-be98-a3b8d7f34bd6

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
theorem _root_.solution (S : QuditSubsystem q) (labels : Qudit.Label q) :
    S.recombineLabel (S.splitLabel labels) = labels :=
  S.labelFactorization.left_inv labels
end QEC.Semantics.QuditSubsystem
