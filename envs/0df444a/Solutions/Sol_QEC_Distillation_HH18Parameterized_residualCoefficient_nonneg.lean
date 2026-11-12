-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.residualCoefficient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:02:35.620112+00:00
-- url     : https://prove2.me/submissions/57751122-6174-45f6-9490-4558c21d9eec

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual

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
theorem _root_.solution (w r m : Nat) :
    0 ≤ residualCoefficient w r m := by
  unfold residualCoefficient
  exact div_nonneg (Nat.cast_nonneg _)
    (le_of_lt (pow_pos (by norm_num) _))
end QEC.Distillation.HH18Parameterized
