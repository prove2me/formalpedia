-- Prove2me | solution 1 for Parikh.wordExpression_star_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:35.713877+00:00
-- url     : https://prove2.me/submissions/1427296f-fd28-49fe-b36a-c9742bdc6ed0

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Definitions.Def_LeanPool_Parikh_RegularRealization
public import Theorems.Thm_Parikh_wordExpression_matches
public import Theorems.Thm_Parikh_counts_append


set_option autoImplicit true
@[expose] public section
public section
open scoped Computability Pointwise
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [DecidableEq T] (w : List T) :
    image (wordExpression w).star.matches' =
      (AddSubmonoid.closure ({counts w} : Set (Vector T)) : Set (Vector T)) := by
  have hrep : ∀ n : ℕ, counts (List.replicate n w).flatten = n • counts w := by
    intro n
    induction n with
    | zero => ext a; simp [counts]
    | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, counts_append, ih, succ_nsmul]
      exact add_comm _ _
  rw [RegularExpression.matches'_star, wordExpression_matches]
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨ws, rfl, hws⟩ := Language.mem_kstar.mp hu
    have hlist : ws = List.replicate ws.length w :=
      List.eq_replicate_of_mem (fun z hz => Set.mem_singleton_iff.mp (hws z hz))
    exact AddSubmonoid.mem_closure_singleton.mpr
      ⟨ws.length, by rw [hlist]; simpa only [List.length_replicate] using (hrep _).symm⟩
  · intro hv
    obtain ⟨n, rfl⟩ := AddSubmonoid.mem_closure_singleton.mp hv
    refine ⟨(List.replicate n w).flatten, Language.join_mem_kstar ?_, hrep n⟩
    intro z hz
    exact Set.mem_singleton_iff.mpr (List.eq_of_mem_replicate hz)
end Parikh
