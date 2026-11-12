-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathTypedSuccessfulOutputCost_denominator_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:36:21.661203+00:00
-- url     : https://prove2.me/submissions/dc47dd3d-706e-455a-9965-8a1e3e0642db

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
theorem _root_.solution (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) :
    0 < (Fintype.card (depthOutputPath q z) : ℝ) *
      bh12PathYieldFactorProduct q p z path := by
  have hslots : 0 < Fintype.card (depthOutputPath q z) :=
    Fintype.card_pos_iff.mpr ⟨path⟩
  exact mul_pos (by exact_mod_cast hslots)
    (bh12PathYieldFactorProduct_pos q p hsmall hhalf hstrong z path)
end QEC.Distillation.Triorthogonal.BH12Concatenation
