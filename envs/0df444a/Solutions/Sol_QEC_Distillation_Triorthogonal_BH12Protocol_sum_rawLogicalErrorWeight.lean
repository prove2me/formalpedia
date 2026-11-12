-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.sum_rawLogicalErrorWeight
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T20:00:33.953167+00:00
-- url     : https://prove2.me/submissions/fd10ec0c-b985-47a2-a1da-58e6d10b9fa3

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

theorem solution (q : Nat) (p : ErrorParameter) :
    ∑ logical : Word (ZMod 2) (OddRow q),
        rawLogicalErrorWeight q p logical = rawSuccessMass q p := by
  classical
  rw [rawSuccessMass]
  simp only [rawLogicalErrorWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro error _
  by_cases haccept : Accepts error
  · simp [haccept]
  · simp [haccept]