-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleActualOutputError_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:58:45.8368+00:00
-- url     : https://prove2.me/submissions/aaa67d8d-932f-4416-9bf8-7a56cb3e32be

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleActualOutputError_exists_path

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
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    0 ≤ routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth := by
  obtain ⟨path, hpath⟩ :=
    routedDepthScheduleActualOutputError_exists_path h hdegree epsilon hsmall depth
  rw [hpath]
  exact (routedDepthPathRate h hdegree epsilon hsmall depth path).property.1
end QEC.Distillation.HH18Parameterized
