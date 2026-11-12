-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.postselectionConditional_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:43:37.783255+00:00
-- url     : https://prove2.me/submissions/5a30c386-63d7-4ea1-92f7-9cb7b0535229

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
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (rho : DensityOperator (PhysicalRegister m w))
    (outcome : DistillationOutcome)
    (hpositive : 0 < postselectionWeight h outcome rho) :
    (postselectionConditional h rho outcome hpositive).toOperator =
      ((postselectionWeight h outcome rho : Complex)⁻¹) •
        rawPostselectionEndpoint h outcome rho :=
  rfl
end QEC.Distillation.HH18Parameterized
