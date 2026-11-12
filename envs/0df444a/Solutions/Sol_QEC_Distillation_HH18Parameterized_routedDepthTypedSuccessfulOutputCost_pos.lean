-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthTypedSuccessfulOutputCost_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:23:11.939106+00:00
-- url     : https://prove2.me/submissions/d0569a27-46cb-4a24-a8bd-6d2370a6d9a6

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPooledYield_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthTypedSuccessfulOutputCost_eq
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthLogicalOutputCount_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPhysicalInputCount_pos


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
    0 < routedDepthTypedSuccessfulOutputCost h hdegree epsilon hsmall depth := by
  rw [routedDepthTypedSuccessfulOutputCost_eq]
  have hinput : 0 < (physicalInputCount m w : ℝ) := by
    exact_mod_cast routedDepthPhysicalInputCount_pos h
  have houtput : 0 < (logicalOutputCount m w : ℝ) := by
    exact_mod_cast routedDepthLogicalOutputCount_pos m w
  exact div_pos (pow_pos (div_pos hinput houtput) _)
    (routedDepthPooledYield_pos h hdegree epsilon hsmall depth)
end QEC.Distillation.HH18Parameterized
