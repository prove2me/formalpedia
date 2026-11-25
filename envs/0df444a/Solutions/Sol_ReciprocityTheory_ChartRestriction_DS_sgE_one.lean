-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sgE_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:10.371194+00:00
-- url     : https://prove2.me/submissions/85985b8a-142b-4901-aafa-15929e36ea5c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (c : Fin n) : sgE ε cpFock cmFock c c (1 : Fock n) = 0 := by
  unfold sgE
  split_ifs <;> simp [cmFock, LinearMap.sum_apply, Module.End.mul_apply, CliffordAlgebra.contractLeft_one]
end ReciprocityTheory.ChartRestriction.DS
