-- Prove2me | solution 1 for Parikh.LinearComponent.isLinearSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:57:13.927864+00:00
-- url     : https://prove2.me/submissions/70647f72-4b3e-4719-88c3-d88190d4f2d0

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
public import Theorems.Thm_Parikh_component_isLinearSet


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
namespace LinearComponent
theorem _root_.solution {T : Type*} (c : LinearComponent T) :
    IsLinearSet c.denotation := component_isLinearSet c
end LinearComponent
end Parikh
