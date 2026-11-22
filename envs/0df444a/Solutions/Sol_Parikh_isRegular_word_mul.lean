-- Prove2me | solution 1 for Parikh.isRegular_word_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:27.281752+00:00
-- url     : https://prove2.me/submissions/d6f47035-938f-4770-976f-c26320c82189

module
public import Mathlib.Computability.DFA
public import Mathlib.Computability.NFA
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
public import Theorems.Thm_Parikh_isRegular_of_finite_language_cover
public import Theorems.Thm_Parikh_mem_word_mul_cons

set_option autoImplicit true
@[expose] public section
public section
open scoped Computability
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution (w : List T) (R : Language T) (hR : R.IsRegular) :
    (({w} : Language T) * R).IsRegular := by
  classical
  obtain ⟨σ, hσ, M, rfl⟩ := hR
  let : Fintype σ := hσ
  let F : Set (Language T) := Set.range M.acceptsFrom ∪
    (fun u => ({u} : Language T) * M.accepts) '' (↑w.tails.toFinset : Set (List T))
  have hF : F.Finite := (Set.finite_range M.acceptsFrom).union
    (w.tails.toFinset.finite_toSet.image _)
  have htail (u : List T) (hu : u <:+ w) : ({u} : Language T) * M.accepts ∈ F := by
    exact Or.inr ⟨u, by simpa using (List.mem_tails u w).mpr hu, rfl⟩
  have hdfa (s : σ) (a : T) (x : List T) (hx : a :: x ∈ M.acceptsFrom s) :
      ∃ J ∈ F, x ∈ J ∧ ∀ v ∈ J, a :: v ∈ M.acceptsFrom s := by
    refine ⟨M.acceptsFrom (M.step s a), Or.inl ⟨_, rfl⟩, ?_, ?_⟩
    · simpa only [DFA.mem_acceptsFrom, DFA.evalFrom_cons] using hx
    · intro v hv
      simpa only [DFA.mem_acceptsFrom, DFA.evalFrom_cons] using hv
  apply isRegular_of_finite_language_cover _ F hF (htail w (List.suffix_refl _))
  intro K hK a x hx
  rcases hK with hK | hK
  · obtain ⟨s, rfl⟩ := hK
    exact hdfa s a x hx
  · obtain ⟨u, hu, rfl⟩ := hK
    have hu : u <:+ w := (List.mem_tails u w).mp (by simpa using hu)
    cases u with
    | nil =>
      change a :: x ∈ (1 : Language T) * M.accepts at hx
      rw [one_mul] at hx
      simpa only [show ({[]} : Language T) = 1 from rfl, one_mul, DFA.accepts] using
        hdfa M.start a x hx
    | cons b u =>
      obtain ⟨hab, hrest⟩ := (mem_word_mul_cons a b u x M.accepts).mp hx
      subst b
      refine ⟨({u} : Language T) * M.accepts,
        htail u ((List.suffix_cons a u).trans hu), hrest, ?_⟩
      intro v hv
      exact (mem_word_mul_cons a a u v M.accepts).mpr ⟨rfl, hv⟩
end Parikh
