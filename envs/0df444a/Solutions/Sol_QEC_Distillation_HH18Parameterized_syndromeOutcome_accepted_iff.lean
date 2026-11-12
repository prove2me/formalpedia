-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.syndromeOutcome_accepted_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:05:59.310935+00:00
-- url     : https://prove2.me/submissions/1b4b5e64-ec39-4b90-8f3c-4a3a55d02b35

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
    syndromeOutcome w r m syndrome = .accepted ↔
      syndrome = HH18PuncturedReedMuller.allPositiveSyndrome w r m := by
  simp [syndromeOutcome]