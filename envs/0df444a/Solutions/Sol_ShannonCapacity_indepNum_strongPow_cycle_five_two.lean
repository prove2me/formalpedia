-- Prove2me | solution 1 for ShannonCapacity.indepNum_strongPow_cycle_five_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:59:17.905938+00:00
-- url     : https://prove2.me/submissions/6759e13c-c52e-4feb-bd1a-4fe79af53348

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Definitions.Def_LovaszTheta_Solution
public import Theorems.Thm_LovaszTheta_indepNum_strongPow_cycle_five_two


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ShannonCapacity
variable {V : Type*}
namespace ShannonCapacity
theorem _root_.solution : (strongPow (cycleGraph 5) 2).indepNum = 5 :=
  LovaszTheta.indepNum_strongPow_cycle_five_two
end ShannonCapacity
