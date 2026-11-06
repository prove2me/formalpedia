-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.split_recombineLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:44:50.318147+00:00
-- url     : https://prove2.me/submissions/3917cd2c-90f7-4efe-9408-703e9d35d825

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
theorem _root_.solution (S : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions × Qudit.Label S.complementDimensions) :
    S.splitLabel (S.recombineLabel labels) = labels :=
  S.labelFactorization.right_inv labels
end QEC.Semantics.QuditSubsystem
