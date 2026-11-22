-- Prove2me | solution 1 for Parikh.parikhImage_isSemilinear_of_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:57:04.918039+00:00
-- url     : https://prove2.me/submissions/0b685e8a-a219-497f-a1c7-98f2342bc304

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
public import Theorems.Thm_Parikh_regular_image


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} [Finite T] [DecidableEq T]
    (L : Language T) (hL : L.IsRegular) : IsSemilinearSet (parikhImage L) := regular_image L hL
end Parikh
