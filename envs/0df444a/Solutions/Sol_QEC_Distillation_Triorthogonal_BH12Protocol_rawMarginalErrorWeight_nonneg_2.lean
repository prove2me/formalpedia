-- Prove2me | solution 2 for QEC.Distillation.Triorthogonal.BH12Protocol.rawMarginalErrorWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:45:11.907552+00:00
-- url     : https://prove2.me/submissions/9335a299-3213-4c10-be95-9d2b1dae30fc

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_rawLogicalErrorWeight_nonneg

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.Triorthogonal.BH12Protocol
theorem _root_.solution (q : Nat) (p : ErrorParameter)
    (a : OddRow q) : 0 ≤ rawMarginalErrorWeight q p a := by
  apply Finset.sum_nonneg
  intro logical _
  split_ifs
  · rfl
  · exact rawLogicalErrorWeight_nonneg q p logical
end QEC.Distillation.Triorthogonal.BH12Protocol
