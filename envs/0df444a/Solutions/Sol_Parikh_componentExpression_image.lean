-- Prove2me | solution 1 for Parikh.componentExpression_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:53:51.445122+00:00
-- url     : https://prove2.me/submissions/428307cb-ff47-4a7d-9d1f-234ec4501c6a

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Theorems.Thm_Parikh_representative_counts
public import Theorems.Thm_Parikh_wordExpression_matches
public import Theorems.Thm_Parikh_image_mul
public import Theorems.Thm_Parikh_periodExpressions_image
public import Theorems.Thm_Parikh_Component_denotation_eq_vadd_closure


set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [DecidableEq T] (alphabet : AlphabetOrder T)
    (c : Component T) :
    image (componentExpression alphabet c).matches' = c.denotation := by
  have hliteral : image (wordExpression (representative alphabet c.base)).matches' =
      {c.base} := by
    rw [wordExpression_matches]
    change counts '' ({representative alphabet c.base} : Set (List T)) = {c.base}
    rw [Set.image_singleton, representative_counts]
  change image ((wordExpression (representative alphabet c.base)).matches' *
    (c.periods.foldr (fun p (rest : RegularExpression T) =>
      .comp (.star (wordExpression (representative alphabet p))) rest) .epsilon).matches') = _
  rw [image_mul, hliteral, periodExpressions_image,
    Component.denotation_eq_vadd_closure]
  ext v
  simp only [Set.mem_add, Set.mem_singleton_iff, Set.mem_vadd_set,
    vadd_eq_add, exists_eq_left]
end Parikh
