-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.one_le_quadraticCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:35:33.488395+00:00
-- url     : https://prove2.me/submissions/902c5cde-294a-4d92-92a0-665be85379ff

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution (q : Nat) : 1 ≤ quadraticCoefficient q := by
  have hcount : (1 : ℝ) ≤ ((1 + 6 * q : Nat) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : 1 + 6 * q ≠ 0))
  unfold quadraticCoefficient
  nlinarith
end QEC.Distillation.Triorthogonal.BH12Concatenation
