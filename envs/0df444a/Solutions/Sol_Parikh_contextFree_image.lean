-- Prove2me | solution 1 for Parikh.contextFree_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:55:03.471171+00:00
-- url     : https://prove2.me/submissions/9b3e28c5-abcc-43f2-b335-ce45f777eb89

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Definitions.Def_LeanPool_Parikh_Statements
public import Theorems.Thm_Parikh_grammar_image

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [Finite T] [DecidableEq T] (L : Language T) (hL : L.IsContextFree) :
    IsSemilinearSet (image L) := by
  obtain ⟨g, rfl⟩ := hL
  exact grammar_image g
end Parikh
