-- Prove2me | solution 1 for SizeRamsey.Plan.cycle4_tau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:06.534621+00:00
-- url     : https://prove2.me/submissions/5bc4c423-f9cb-4bab-b3b6-adb7ab0aec0d

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Theorems.Thm_SizeRamsey_Plan_cycle4Pres_spec
public import Theorems.Thm_SizeRamsey_Plan_prescribedOptimal_of_table
public import Theorems.Thm_SizeRamsey_Plan_not_c4Transversal_of_card_lt_one


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
namespace SizeRamsey.Plan
theorem _root_.solution : tau4 (SimpleGraph.cycleGraph 4) = 1 ∧
    PrescribedOptimal (SimpleGraph.cycleGraph 4) :=
  prescribedOptimal_of_table 1 cycle4Pres cycle4Pres_spec
    (not_c4Transversal_of_card_lt_one (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) 0
end SizeRamsey.Plan
