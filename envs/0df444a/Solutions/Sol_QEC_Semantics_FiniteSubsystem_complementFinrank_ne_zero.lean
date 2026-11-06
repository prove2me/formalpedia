-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.complementFinrank_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:42:59.976365+00:00
-- url     : https://prove2.me/submissions/e8206993-77dc-4eb4-b715-1ac5c0565a02

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
namespace QEC.Semantics.FiniteSubsystem
theorem _root_.solution (S : FiniteSubsystem ι) :
    (Module.finrank Complex S.complementSystem : Complex) ≠ 0 := by
  rw [Qubit.finrank_qubitRegister]
  norm_cast
  exact Nat.ne_of_gt (Nat.pow_pos (by norm_num : 0 < (2 : Nat)))
end QEC.Semantics.FiniteSubsystem
