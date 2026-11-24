-- Prove2me | solution 1 for Psi.splitAtRow_fst_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:40:55.36519+00:00
-- url     : https://prove2.me/submissions/be2cdac6-7c34-4914-a926-a2ad23141baf

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h : ℕ) :
    (splitAtRow p h).1 = [] ∨ (splitAtRow p h).1.head? = p.head? := by
  fun_induction splitAtRow p h with
  | case1 p => left; rfl
  | case2 h => left; rfl
  | case3 rest => right; rfl
  | case4 rest hx => right; rfl
  | case5 rest h ρ ρ' heq ih => right; rw [heq] at *; rfl
  | case6 rest h ρ ρ' heq ih => right; rw [heq] at *; rfl
end Psi
