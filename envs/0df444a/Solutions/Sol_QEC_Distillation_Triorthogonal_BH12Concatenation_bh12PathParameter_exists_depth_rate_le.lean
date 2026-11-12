-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathParameter_exists_depth_rate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:39:50.424467+00:00
-- url     : https://prove2.me/submissions/47d6945e-7710-4978-9b4f-16341d383c52

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathParameter_rate_le_quadraticEnvelope
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12QuadraticEnvelope_exists_le

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
    (hstrict : quadraticCoefficient q * p.rate < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ z : Nat, ∀ path : depthOutputPath q z,
      (bh12PathParameter q p z path).rate ≤ epsilon := by
  obtain ⟨z, henvelope⟩ :=
    bh12QuadraticEnvelope_exists_le q p hstrict epsilon hepsilon
  refine ⟨z, ?_⟩
  intro path
  exact (bh12PathParameter_rate_le_quadraticEnvelope q p hsmall hhalf
    hquadraticSmall z path).trans henvelope
end QEC.Distillation.Triorthogonal.BH12Concatenation
