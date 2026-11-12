-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.noisyInput_eq_independentNoisyTRegister
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T18:37:24.676701+00:00
-- url     : https://prove2.me/submissions/6f781e08-e456-4d1e-bf79-bfcff6224369

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

theorem solution
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (m w : Nat) :
    noisyInput epsilon m w =
      HH18NoisyInput.independentNoisyTRegister
        (ι := PhysicalSite m w) epsilon := rfl