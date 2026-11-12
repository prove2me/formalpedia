-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathYieldFactor_eq_flaggedYieldFraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:35:26.803089+00:00
-- url     : https://prove2.me/submissions/a64cfb98-c0eb-4b7c-aa7f-4edef04cd0b6

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PhysicalExpectedAcceptedPorts

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution (q : Nat)
    (p : ErrorParameter) (z : Nat) (path : depthOutputPath q z) (stage : Fin z) :
    bh12PathYieldFactor q p z path stage =
      DependentBatch.expectedAcceptedPorts (bh12PhysicalFlaggedBatch q
        (bh12PathParameter q p stage.1 (bh12PathStage q z path stage))) /
        (bh12OutputCount q : ℝ) := by
  have hq : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hqzero
    subst q
    exact Fin.elim0 (path stage).1
  have hkNat : 0 < bh12OutputCount q := by
    change 0 < 2 * q
    omega
  have hk : (bh12OutputCount q : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hkNat)
  rw [bh12PhysicalExpectedAcceptedPorts]
  unfold bh12PathYieldFactor
  apply (eq_div_iff hk).2
  ring
end QEC.Distillation.Triorthogonal.BH12Concatenation
