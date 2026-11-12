-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.syndromeOutcome_rejected_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:01:09.746164+00:00
-- url     : https://prove2.me/submissions/e97cf13d-aebb-428f-9386-b6fa7cc2604a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem solution (w r m : Nat) (syndrome : Syndrome w r m) :
    syndromeOutcome w r m syndrome = .rejected ↔
      syndrome ≠ HH18PuncturedReedMuller.allPositiveSyndrome w r m := by
  simp [syndromeOutcome]