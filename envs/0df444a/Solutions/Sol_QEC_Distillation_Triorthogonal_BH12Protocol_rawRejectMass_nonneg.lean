-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.rawRejectMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:28:57.449554+00:00
-- url     : https://prove2.me/submissions/a54b24dd-2860-4dd5-8ef3-dc9681aa94a3

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
theorem _root_.solution (q : Nat) (p : ErrorParameter) :
    0 ≤ rawRejectMass q p := by
  apply Finset.sum_nonneg
  intro error _
  split_ifs
  · rfl
  · exact errorWordProbability_nonneg p error
end QEC.Distillation.Triorthogonal.BH12Protocol
