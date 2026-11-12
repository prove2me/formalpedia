-- Prove2me | solution 1 for QEC.Distillation.HH18Postselection.postselectionConditional_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:44:53.838146+00:00
-- url     : https://prove2.me/submissions/06d9a572-2f4c-4498-897c-3afe9ea3b27b

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Postselection

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Postselection
open Coding Semantics
open Coding.PauliSymplectic
open HH18SyndromeDecoding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.HH18Postselection
theorem _root_.solution
    (rho : DensityOperator PhysicalRegister) (outcome : DistillationOutcome)
    (hpos : 0 < postselectionWeight outcome rho) :
    (postselectionConditional rho outcome hpos).toOperator =
      ((postselectionWeight outcome rho : Complex)⁻¹) •
        rawPostselectionEndpoint outcome rho :=
  rfl
end QEC.Distillation.HH18Postselection
