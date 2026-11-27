-- Prove2me | solution 1 for SizeRamsey.Plan.wheel5_tau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:10.96662+00:00
-- url     : https://prove2.me/submissions/8c4b31c4-5008-485f-83b5-47b197b3dc85

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Theorems.Thm_SizeRamsey_Plan_wheel5Pres_spec
public import Theorems.Thm_SizeRamsey_Plan_wheel5_avoid_one
public import Theorems.Thm_SizeRamsey_Plan_prescribedOptimal_of_table
public import Theorems.Thm_SizeRamsey_Plan_not_c4Transversal_of_avoid_one


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
namespace SizeRamsey.Plan
theorem _root_.solution : tau4 wheel5 = 2 ∧ PrescribedOptimal wheel5 :=
  prescribedOptimal_of_table 2 wheel5Pres wheel5Pres_spec
    (not_c4Transversal_of_avoid_one 0 wheel5_avoid_one) 0
end SizeRamsey.Plan
