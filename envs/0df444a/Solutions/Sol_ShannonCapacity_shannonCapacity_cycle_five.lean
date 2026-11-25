-- Prove2me | solution 1 for ShannonCapacity.shannonCapacity_cycle_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:08:06.954179+00:00
-- url     : https://prove2.me/submissions/385f3d41-1c79-4215-9c13-fe3fff4a3581

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Definitions.Def_LovaszTheta_Solution
public import Theorems.Thm_LovaszTheta_shannonCapacity_cycle_five


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ShannonCapacity
variable {V : Type*}
namespace ShannonCapacity
theorem _root_.solution : shannonCapacity (cycleGraph 5) = Real.sqrt 5 :=
  LovaszTheta.shannonCapacity_cycle_five
end ShannonCapacity
