-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathUniformPhysicalTarget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:43:00.823569+00:00
-- url     : https://prove2.me/submissions/dd69e123-885c-42d0-8a2a-db1d0bf3a161

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathParameter_success
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSelectedPortTransportedDensity_eq_diagonalAResource
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathParameter_exists_depth_rate_le

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
      0 < rawSuccessMass q (bh12PathParameter q p z path) ∧
        0 < (bh12PathRun q p z path).successProbability ∧
          (∀ port : OddRow q,
            bh12PathSelectedPortTransportedDensity q p z path port =
              OneQubit.diagonalAResource
                (bh12TotalNextParameter q (bh12PathParameter q p z path) port)) ∧
            (bh12PathParameter q p z path).rate ≤ epsilon := by
  obtain ⟨z, hrate⟩ := bh12PathParameter_exists_depth_rate_le q p hsmall hhalf
    hquadraticSmall hstrict epsilon hepsilon
  refine ⟨z, ?_⟩
  intro path
  have hsuccess : 0 < rawSuccessMass q (bh12PathParameter q p z path) :=
    bh12PathParameter_success q p hsmall hhalf hquadraticSmall z path
  refine ⟨hsuccess, ?_, ?_, hrate path⟩
  · change 0 < (bh12ActualRun q (bh12PathParameter q p z path)).successProbability
    rw [bh12ActualRun_successProbability]
    exact hsuccess
  · intro port
    exact bh12PathSelectedPortTransportedDensity_eq_diagonalAResource q p
      hsmall hhalf hquadraticSmall z path port
end QEC.Distillation.Triorthogonal.BH12Concatenation
