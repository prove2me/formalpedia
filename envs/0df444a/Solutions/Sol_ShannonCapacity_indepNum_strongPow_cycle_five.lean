-- Prove2me | solution 1 for ShannonCapacity.indepNum_strongPow_cycle_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:51:11.545936+00:00
-- url     : https://prove2.me/submissions/250b7bcd-c321-477a-a8b0-9ca617af1712

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Definitions.Def_LovaszTheta_Solution
public import Theorems.Thm_LovaszTheta_indepNum_strongPow_cycle_five


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ShannonCapacity
variable {V : Type*}
namespace ShannonCapacity
theorem _root_.solution (k : ℕ) :
    (strongPow (cycleGraph 5) k).indepNum ^ 2 ≤ 5 ^ k :=
  LovaszTheta.indepNum_strongPow_cycle_five k
end ShannonCapacity
