-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.rawLogicalErrorWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:04:27.070281+00:00
-- url     : https://prove2.me/submissions/c94fede8-f9a0-4ac5-bfc3-c50ef0395727

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol

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
    (logical : Word (ZMod 2) (OddRow q)) :
    0 ≤ rawLogicalErrorWeight q p logical := by
  apply Finset.sum_nonneg
  intro error _
  split_ifs
  · exact errorWordProbability_nonneg p error
  · rfl
end QEC.Distillation.Triorthogonal.BH12Protocol
