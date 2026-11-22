-- Prove2me | solution 1 for Parikh.witnessExpression_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:54:26.826213+00:00
-- url     : https://prove2.me/submissions/64bfdb6a-4290-41bf-803c-5e353be7b8c7

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Theorems.Thm_Parikh_componentExpression_image

set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [DecidableEq T] (alphabet : AlphabetOrder T) (W : Witness T) :
    image (witnessExpression alphabet W).matches' = W.denotation := by
  induction W with
  | nil => ext v; simp [witnessExpression, RegularExpression.matches', image,
      Language.zero_def, Witness.denotation]
  | cons c W ih =>
    have hcons : Witness.denotation (c :: W) = c.denotation ∪ Witness.denotation W := by
      ext v
      simp [Witness.denotation]
    have hunion : image ((componentExpression alphabet c).matches' +
        (witnessExpression alphabet W).matches') =
        image (componentExpression alphabet c).matches' ∪
          image (witnessExpression alphabet W).matches' :=
      Set.image_union counts _ _
    change image ((componentExpression alphabet c).matches' +
      (witnessExpression alphabet W).matches') = _
    rw [hunion]
    rw [componentExpression_image, ih, hcons]
end Parikh
