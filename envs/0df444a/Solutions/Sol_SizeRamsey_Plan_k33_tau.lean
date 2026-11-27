-- Prove2me | solution 1 for SizeRamsey.Plan.k33_tau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:12.782934+00:00
-- url     : https://prove2.me/submissions/c0fc81e0-8bc9-44b8-9c03-c762611c73a7

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Theorems.Thm_SizeRamsey_Plan_k33Pres_spec
public import Theorems.Thm_SizeRamsey_Plan_k33_avoid_one
public import Theorems.Thm_SizeRamsey_Plan_prescribedOptimal_of_table
public import Theorems.Thm_SizeRamsey_Plan_not_c4Transversal_of_avoid_one


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
namespace SizeRamsey.Plan
theorem _root_.solution : tau4 k33MinusEdge = 2 ∧ PrescribedOptimal k33MinusEdge :=
  prescribedOptimal_of_table 2 k33Pres k33Pres_spec
    (not_c4Transversal_of_avoid_one 0 k33_avoid_one) 0
end SizeRamsey.Plan
