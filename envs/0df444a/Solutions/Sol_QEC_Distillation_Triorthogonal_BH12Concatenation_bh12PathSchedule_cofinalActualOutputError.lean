-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_cofinalActualOutputError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:45:30.511936+00:00
-- url     : https://prove2.me/submissions/0453b554-68ab-4a7a-8d6f-b2b964e542b1

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathUniformPhysicalTarget

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
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ z : Nat, ∀ path : depthOutputPath q z,
      0 < rawSuccessMass q (bh12PathParameter q p z path) ∧
        0 < (bh12PathRun q p z path).successProbability ∧
          (∀ port : OddRow q,
            bh12PathSelectedPortTransportedDensity q p z path port =
              OneQubit.diagonalAResource
                (bh12TotalNextParameter q (bh12PathParameter q p z path) port)) ∧
            (bh12PathParameter q p z path).rate ≤ epsilon := by
  exact bh12PathUniformPhysicalTarget q p hsmall hhalf
    (hstrong.trans (by norm_num))
    (hstrong.trans_lt (by norm_num)) epsilon hepsilon
end QEC.Distillation.Triorthogonal.BH12Concatenation
