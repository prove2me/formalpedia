-- Prove2me | solution 1 for Parikh.EncodedGrammar.activeLabels_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:32.587651+00:00
-- url     : https://prove2.me/submissions/6923a1a0-a167-4d6e-991d-4f474b1225ba

module
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Definitions.Def_LeanPool_Parikh_BoundedEnumeration
public import Definitions.Def_LeanPool_Parikh_CompilerTrees

set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar
namespace Parikh.EncodedGrammar
theorem _root_.solution (g : EncodedGrammar) :
    g.activeLabels = activeNonterminals g.decode := by
  classical
  unfold activeLabels activeNonterminals
  have heq : (fun a b : g.decode.NT => Classical.propDecidable (a = b)) =
      instDecidableEqFin (g.extraNonterminalCount + 1) := Subsingleton.elim _ _
  rw [heq]
  congr 3
  funext r
  congr 3
  funext s
  cases s <;> rfl
end Parikh.EncodedGrammar
