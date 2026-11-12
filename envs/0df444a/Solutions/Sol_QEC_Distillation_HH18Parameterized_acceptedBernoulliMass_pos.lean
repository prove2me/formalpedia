-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.acceptedBernoulliMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:43:14.388203+00:00
-- url     : https://prove2.me/submissions/589c6610-1474-4339-a497-1536800de61e

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedBernoulliMass_allZeroWord_le

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
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < acceptedBernoulliMass w r m epsilon := by
  have hfactor : 0 < 1 - epsilon.1 := by
    linarith [epsilon.property.2]
  exact lt_of_lt_of_le (pow_pos hfactor _)
    (acceptedBernoulliMass_allZeroWord_le h epsilon)
end QEC.Distillation.HH18Parameterized
