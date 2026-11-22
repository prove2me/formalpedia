-- Prove2me | solution 1 for Parikh.periodExpressions_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:53:14.288328+00:00
-- url     : https://prove2.me/submissions/1d48a0d9-978d-4a68-8698-14c13b64c8d9

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Theorems.Thm_Parikh_representative_counts
public import Theorems.Thm_Parikh_image_mul
public import Theorems.Thm_Parikh_wordExpression_star_image

set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [DecidableEq T] (alphabet : AlphabetOrder T)
    (periods : List (Vector T)) :
    image (periods.foldr (fun p (rest : RegularExpression T) =>
      .comp (.star (wordExpression (representative alphabet p))) rest) .epsilon).matches' =
      (AddSubmonoid.closure (Set.range periods.get) : Set (Vector T)) := by
  induction periods with
  | nil =>
    have hnil : counts ([] : List T) = 0 := by ext a; simp [counts]
    ext v
    simp [image, RegularExpression.matches', Language.one_def,
      Set.range_eq_empty, AddSubmonoid.closure_empty, hnil]
  | cons p ps ih =>
    have hrange : Set.range (p :: ps).get = {p} ∪ Set.range ps.get := by
      rw [Set.range_list_get, Set.range_list_get]
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, List.mem_cons]
    rw [hrange, AddSubmonoid.closure_union]
    change image ((wordExpression (representative alphabet p)).star.matches' *
      (ps.foldr (fun q (rest : RegularExpression T) =>
        .comp (.star (wordExpression (representative alphabet q))) rest) .epsilon).matches') = _
    rw [image_mul, wordExpression_star_image, representative_counts, ih]
    ext v
    simp only [Set.mem_add, SetLike.mem_coe, AddSubmonoid.mem_sup]
end Parikh
