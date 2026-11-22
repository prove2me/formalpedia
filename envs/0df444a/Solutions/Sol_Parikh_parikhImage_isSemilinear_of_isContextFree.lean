-- Prove2me | solution 1 for Parikh.parikhImage_isSemilinear_of_isContextFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:57:03.862113+00:00
-- url     : https://prove2.me/submissions/6edf77db-308d-4b74-b482-e7011195db22

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
public import Theorems.Thm_Parikh_contextFree_image


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} [Finite T] [DecidableEq T]
    (L : Language T) (hL : L.IsContextFree) : IsSemilinearSet (parikhImage L) :=
  contextFree_image L hL
end Parikh
