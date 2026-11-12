-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathParameter_success
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:26:20.591599+00:00
-- url     : https://prove2.me/submissions/1a64ee64-2cae-439b-977f-56f2ac4a18e0

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
theorem _root_.solution (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1)
    (z : Nat) (path : depthOutputPath q z) :
    0 < rawSuccessMass q (bh12PathParameter q p z path) := by
  obtain ⟨hpathSmall, _hpathHalf, _hpathCoefficient⟩ :=
    bh12PathParameter_admissible q p hsmall hhalf hquadraticSmall z path
  rw [← bh12ActualRun_successProbability]
  exact bh12ActualRun_successProbability_pos_of_small_error q
    (bh12PathParameter q p z path) hpathSmall
end QEC.Distillation.Triorthogonal.BH12Concatenation
