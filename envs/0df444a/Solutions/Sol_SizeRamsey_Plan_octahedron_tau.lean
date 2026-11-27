-- Prove2me | solution 1 for SizeRamsey.Plan.octahedron_tau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:22.104337+00:00
-- url     : https://prove2.me/submissions/489e4960-7e74-42c3-9389-22bc4d4ea99e

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Theorems.Thm_SizeRamsey_Plan_octahedronPres_spec
public import Theorems.Thm_SizeRamsey_Plan_octahedron_avoid_pair
public import Theorems.Thm_SizeRamsey_Plan_prescribedOptimal_of_table
public import Theorems.Thm_SizeRamsey_Plan_not_c4Transversal_of_avoid_pair


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
namespace SizeRamsey.Plan
theorem _root_.solution : tau4 octahedron = 3 ∧ PrescribedOptimal octahedron :=
  prescribedOptimal_of_table 3 octahedronPres octahedronPres_spec
    (not_c4Transversal_of_avoid_pair 0 octahedron_avoid_pair) 0
end SizeRamsey.Plan
