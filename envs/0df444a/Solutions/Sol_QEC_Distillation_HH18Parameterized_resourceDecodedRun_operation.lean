-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.resourceDecodedRun_operation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:45:37.566398+00:00
-- url     : https://prove2.me/submissions/1cb70e5c-6414-4a02-a991-61c469328e7f

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun

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
attribute [local instance] QEC.Distillation.HH18Parameterized.instNormalizedRunClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    (resourceDecodedRun h hdegree inputs).operation = decodedOperation h hdegree :=
  rfl
end QEC.Distillation.HH18Parameterized
