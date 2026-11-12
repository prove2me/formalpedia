-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.logicalPlus_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:54:50.704078+00:00
-- url     : https://prove2.me/submissions/69771c67-9f26-4ba7-8970-707b12e62d58

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_inner_self


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution (m w : Nat) : ‖logicalPlus m w‖ = 1 := by
  have hinner := Triorthogonal.BinaryRowFamily.logicalPlusState_inner_self
    (LogicalSite m w)
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsquare : ‖logicalPlus m w‖ ^ 2 = 1 := by
    change ‖Triorthogonal.BinaryRowFamily.logicalPlusState (LogicalSite m w)‖ ^ 2 = 1
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow]
    exact hinner
  nlinarith [norm_nonneg (logicalPlus m w)]
end QEC.Distillation.HH18Parameterized
