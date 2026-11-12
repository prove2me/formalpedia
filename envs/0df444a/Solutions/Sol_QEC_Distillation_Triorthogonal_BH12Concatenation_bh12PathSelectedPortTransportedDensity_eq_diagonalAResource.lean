-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSelectedPortTransportedDensity_eq_diagonalAResource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:30:17.458085+00:00
-- url     : https://prove2.me/submissions/7e00b3fa-3b0b-48dd-a8b9-6935b8944857

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathParameter_success

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution
    (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1)
    (z : Nat) (path : depthOutputPath q z) (port : OddRow q) :
    bh12PathSelectedPortTransportedDensity q p z path port =
      OneQubit.diagonalAResource
        (bh12TotalNextParameter q (bh12PathParameter q p z path) port) := by
  have hsuccess : 0 < rawSuccessMass q (bh12PathParameter q p z path) :=
    bh12PathParameter_success q p hsmall hhalf hquadraticSmall z path
  change bh12SelectedPortTransportedDensity q (bh12PathParameter q p z path) port = _
  rw [bh12TotalNextParameter_of_success q (bh12PathParameter q p z path)
    port hsuccess]
  exact bh12SelectedPortTransportedDensity_eq_diagonalAResource q
    (bh12PathParameter q p z path) hsuccess port
end QEC.Distillation.Triorthogonal.BH12Concatenation
