-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.noisyResources_permitted
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:10:26.383746+00:00
-- url     : https://prove2.me/submissions/b37a0bfa-91c3-47fa-ba10-bc69a3998130

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem solution (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    InputErrorModel.Permits (.independent (independentInputModel m w epsilon))
      (noisyResources m w epsilon) := by
  constructor
  · intro slot
    rfl
  · rfl