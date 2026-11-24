-- Prove2me | solution 1 for Psi.splitAtRow_fst_ne_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:41:04.281311+00:00
-- url     : https://prove2.me/submissions/e9b72956-8dee-413a-b6b0-4645dd379960

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h : ℕ) (hh : h ≠ 0) (hp : p ≠ []) :
    (splitAtRow p h).1 ≠ [] := by
  fun_induction splitAtRow p h with
  | case1 p => omega
  | case2 h => simp at hp
  | case3 rest => simp
  | case4 rest hx => simp
  | case5 rest h ρ ρ' heq ih => rw [heq] at *; simp
  | case6 rest h ρ ρ' heq ih => rw [heq] at *; simp
end Psi
