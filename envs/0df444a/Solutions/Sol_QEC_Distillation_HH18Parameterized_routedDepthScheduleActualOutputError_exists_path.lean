-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleActualOutputError_exists_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:08:07.463972+00:00
-- url     : https://prove2.me/submissions/53213b28-ae18-4563-b6b8-48b594b24925

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthOutputSlots_nonempty


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
    ∃ path : routedDepthOutputSlots m w depth,
      routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth =
        (routedDepthPathRate h hdegree epsilon hsmall depth path).1 := by
  classical
  unfold routedDepthScheduleActualOutputError
  obtain ⟨path, _, hpath⟩ := Finset.exists_mem_eq_sup'
    ⟨(routedDepthOutputSlots_nonempty m w depth).some, Finset.mem_univ _⟩
    (fun path => (routedDepthPathRate h hdegree epsilon hsmall depth path).1)
  exact ⟨path, hpath⟩
end QEC.Distillation.HH18Parameterized
