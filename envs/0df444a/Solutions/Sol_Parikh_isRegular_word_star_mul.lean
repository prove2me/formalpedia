-- Prove2me | solution 1 for Parikh.isRegular_word_star_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:36.98993+00:00
-- url     : https://prove2.me/submissions/b55a2ecc-1e6c-48bb-b0b1-aadfa49d33ca

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
    (({w} : Language T)∗ * R).IsRegular := by
  classical
  cases w with
  | nil =>
    simpa only [show ({[]} : Language T) = 1 from rfl, kstar_one, one_mul] using hR
  | cons b bs =>
    obtain ⟨σ, hσ, M, rfl⟩ := hR
    let : Fintype σ := hσ
    let S : Language T := ({b :: bs} : Language T)∗ * M.accepts
    let F : Set (Language T) := Set.range M.acceptsFrom ∪
      (fun u => ({u} : Language T) * S) '' (↑(b :: bs).tails.toFinset : Set (List T))
    have hF : F.Finite := (Set.finite_range M.acceptsFrom).union
      ((b :: bs).tails.toFinset.finite_toSet.image _)
    have htail (u : List T) (hu : u <:+ b :: bs) : ({u} : Language T) * S ∈ F := by
      exact Or.inr ⟨u, by simpa using (List.mem_tails u (b :: bs)).mpr hu, rfl⟩
    have hdfa (s : σ) (a : T) (x : List T) (hx : a :: x ∈ M.acceptsFrom s) :
        ∃ J ∈ F, x ∈ J ∧ ∀ v ∈ J, a :: v ∈ M.acceptsFrom s := by
      refine ⟨M.acceptsFrom (M.step s a), Or.inl ⟨_, rfl⟩, ?_, ?_⟩
      · simpa only [DFA.mem_acceptsFrom, DFA.evalFrom_cons] using hx
      · intro v hv
        simpa only [DFA.mem_acceptsFrom, DFA.evalFrom_cons] using hv
    have hunfold : S = M.accepts + ({b :: bs} : Language T) * S := by
      dsimp [S]
      conv_lhs => rw [← Language.one_add_self_mul_kstar_eq_kstar ({b :: bs} : Language T)]
      rw [add_mul, one_mul, mul_assoc]
    have hstart : S ∈ F := by
      simpa only [show ({[]} : Language T) = 1 from rfl, one_mul] using
        htail [] List.nil_suffix
    apply isRegular_of_finite_language_cover S F hF hstart
    intro K hK a x hx
    rcases hK with hK | hK
    · obtain ⟨s, rfl⟩ := hK
      exact hdfa s a x hx
    · obtain ⟨u, hu, rfl⟩ := hK
      have hu : u <:+ b :: bs := (List.mem_tails u (b :: bs)).mp (by simpa using hu)
      cases u with
      | nil =>
        change a :: x ∈ (1 : Language T) * S at hx
        rw [one_mul, hunfold, Language.mem_add] at hx
        change ∃ J ∈ F, x ∈ J ∧ ∀ v ∈ J, a :: v ∈ (1 : Language T) * S
        simp only [one_mul]
        rcases hx with hx | hx
        · obtain ⟨J, hJ, hx, hs⟩ := hdfa M.start a x hx
          refine ⟨J, hJ, hx, ?_⟩
          intro v hv
          rw [hunfold, Language.mem_add]
          exact Or.inl (hs v hv)
        · obtain ⟨hab, hrest⟩ := (mem_word_mul_cons a b bs x S).mp hx
          subst b
          refine ⟨({bs} : Language T) * S, htail bs (List.suffix_cons a bs), hrest, ?_⟩
          intro v hv
          rw [hunfold, Language.mem_add]
          exact Or.inr ((mem_word_mul_cons a a bs v S).mpr ⟨rfl, hv⟩)
      | cons c u =>
        obtain ⟨hac, hrest⟩ := (mem_word_mul_cons a c u x S).mp hx
        subst c
        refine ⟨({u} : Language T) * S,
          htail u ((List.suffix_cons a u).trans hu), hrest, ?_⟩
        intro v hv
        exact (mem_word_mul_cons a a u v S).mpr ⟨rfl, hv⟩
end Parikh
