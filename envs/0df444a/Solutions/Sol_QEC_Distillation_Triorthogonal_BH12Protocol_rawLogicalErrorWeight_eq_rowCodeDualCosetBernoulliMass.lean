-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.rawLogicalErrorWeight_eq_rowCodeDualCosetBernoulliMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:29:22.271732+00:00
-- url     : https://prove2.me/submissions/00492b1d-01c9-4fee-94ca-d8e95e72cb6b

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_accepts_and_logicalErrorWord_eq_iff_mem_rowCodeDualCoset

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
theorem _root_.solution (q : Nat)
    (p : ErrorParameter) (logical : Word (ZMod 2) (OddRow q)) :
    rawLogicalErrorWeight q p logical =
      rowCodeDualCosetBernoulliMass q p logical := by
  classical
  unfold rawLogicalErrorWeight rowCodeDualCosetBernoulliMass
  apply Finset.sum_congr rfl
  intro error _
  by_cases hcoset : error - (family q).oddCombination logical ∈
      (family q).rowCode.dual.carrier
  · have hlogical : Accepts error ∧ logicalErrorWord error = logical :=
      (accepts_and_logicalErrorWord_eq_iff_mem_rowCodeDualCoset
        q error logical).mpr hcoset
    rw [if_pos hlogical, if_pos hcoset]
  · have hlogical : ¬(Accepts error ∧ logicalErrorWord error = logical) := by
      intro hlogical
      exact hcoset
        ((accepts_and_logicalErrorWord_eq_iff_mem_rowCodeDualCoset
          q error logical).mp hlogical)
    rw [if_neg hlogical, if_neg hcoset]
end QEC.Distillation.Triorthogonal.BH12Protocol
