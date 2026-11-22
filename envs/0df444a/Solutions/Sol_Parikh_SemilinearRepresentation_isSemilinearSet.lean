-- Prove2me | solution 1 for Parikh.SemilinearRepresentation.isSemilinearSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:57:01.792121+00:00
-- url     : https://prove2.me/submissions/4b310ea9-8ba0-4703-b591-af4597e8e693

module
public import Definitions.Def_LeanPool_Parikh_ExecutableCompiler
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Definitions.Def_LeanPool_Parikh_Api
public import Theorems.Thm_Parikh_witness_isSemilinearSet


set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
namespace SemilinearRepresentation
theorem _root_.solution {T : Type*}
    (W : SemilinearRepresentation T) : IsSemilinearSet W.denotation := witness_isSemilinearSet W
end SemilinearRepresentation
end Parikh
