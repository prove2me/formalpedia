-- Prove2me | solution 2 for QEC.Distillation.HH18Parameterized.noisyInput_eq_independentNoisyTRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:38:07.7552+00:00
-- url     : https://prove2.me/submissions/4b571cb9-eb40-42ea-b405-fb7609b00d39

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
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (m w : Nat) :
    noisyInput epsilon m w =
      HH18NoisyInput.independentNoisyTRegister
        (ι := PhysicalSite m w) epsilon :=
  rfl
end QEC.Distillation.HH18Parameterized
