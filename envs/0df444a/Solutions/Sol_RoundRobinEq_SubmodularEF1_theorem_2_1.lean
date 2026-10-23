-- Prove2me | solution 1 for RoundRobinEq.SubmodularEF1.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T03:32:42.28899+00:00
-- url     : https://prove2.me/submissions/5225f278-5f41-4b2a-95fd-074aab99d004

/-
Submodular marginal-sum characterization, 23 October 2026.
Original characterization: Nemhauser, Wolsey and Fisher (1978), as reproduced
in Amanatidis, Birmpas, Lazos, Leonardi and Reiffenhäuser, Round-Robin Beyond
Additive Agents, arXiv:2301.13652v1, Theorem 2.1, printed p.5. The 1978 original
was not inspected. mikedeng1 supplied the platform definitions and target;
Shuze Chen's statement approval is not review of this proof.
Alexander Richard Towell directed the campaign; OpenAI Codex constructed and
checked the proof. Lean/Mathlib supply finite-set and ordered-field foundations.
No prior platform proof is reused. No mathematical novelty or independent
human review is claimed. The argument does not require normalization.
-/
import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularEF1_Setting

open RoundRobinEq.SubmodularEF1

namespace MarginalSumProof

variable {M : Type} [Fintype M] [DecidableEq M] (v : Finset M → ℝ)

lemma union_bound (hsub : IsSubmodular v) (S U : Finset M) :
    v (S ∪ U) ≤ v S + ∑ g ∈ U, marginal v {g} S := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert x U hx ih =>
    rw [Finset.sum_insert hx]
    by_cases hxS : x ∈ S
    · have heq : S ∪ insert x U = S ∪ U := by ext a; simp; aesop
      have hmarg : marginal v {x} S = 0 := by simp [marginal, hxS]
      simpa [heq, hmarg] using ih
    · have hxSU : x ∉ S ∪ U := by simp [hxS, hx]
      have h := hsub S (S ∪ U) x Finset.subset_union_left hxSU
      have heq : S ∪ insert x U = insert x (S ∪ U) := by ext a; simp
      rw [heq]
      simp only [marginal, Finset.singleton_union] at h ih ⊢
      linarith

lemma one_step (h : ∀ S T : Finset M,
    v T ≤ v S + ∑ g ∈ T \ S, marginal v {g} S)
    (S : Finset M) (x g : M) (hx : x ∉ S) (hg : g ∉ S) (hxg : x ≠ g) :
    marginal v {g} (insert x S) ≤ marginal v {g} S := by
  have hpair := h S (insert x (insert g S))
  have hdiff : insert x (insert g S) \ S = {x, g} := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [hdiff] at hpair
  simp only [Finset.sum_insert (show x ∉ ({g} : Finset M) by simpa using hxg),
    Finset.sum_singleton, marginal, Finset.singleton_union] at hpair ⊢
  rw [Finset.insert_comm] at hpair
  linarith

lemma diminishing (h : ∀ S T : Finset M,
    v T ≤ v S + ∑ g ∈ T \ S, marginal v {g} S)
    (S U : Finset M) (g : M) (hg : g ∉ S ∪ U) :
    marginal v {g} (S ∪ U) ≤ marginal v {g} S := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert x U hx ih =>
    have hgU : g ∉ S ∪ U := by intro hmem; apply hg; simpa only [Finset.mem_union,
      Finset.mem_insert] using (show g ∈ S ∪ insert x U from Finset.mem_union.mpr
        ((Finset.mem_union.mp hmem).imp_right (fun h => Finset.mem_insert_of_mem h)))
    have ih' := ih hgU
    have heq : S ∪ insert x U = insert x (S ∪ U) := by ext a; simp
    rw [heq]
    by_cases hxSU : x ∈ S ∪ U
    · simpa [Finset.insert_eq_of_mem hxSU] using ih'
    · have hxg : x ≠ g := by intro he; subst x; apply hg; simp
      exact (one_step v h (S ∪ U) x g hxSU hgU hxg).trans ih'

end MarginalSumProof

theorem solution {M : Type} [Fintype M] [DecidableEq M] (v : Finset M → ℝ)
    (hv : ∀ S, 0 ≤ v S) :
    (IsNonDecreasing v ∧ IsSubmodular v) ↔
      ∀ S T : Finset M, v T ≤ v S + ∑ g ∈ T \ S, marginal v {g} S := by
  constructor
  · rintro ⟨hmono, hsub⟩ S T
    have hle := hmono T (S ∪ (T \ S)) (by intro x hx; simp; aesop)
    exact hle.trans (MarginalSumProof.union_bound v hsub S (T \ S))
  · intro h
    constructor
    · intro S T hST
      have h' := h T S
      simpa [Finset.sdiff_eq_empty_iff_subset.mpr hST] using h'
    · intro S T g hST hg
      have hg' : g ∉ S ∪ (T \ S) := by simpa [Finset.union_sdiff_of_subset hST] using hg
      simpa [Finset.union_sdiff_of_subset hST] using
        MarginalSumProof.diminishing v h S (T \ S) g hg'

#print axioms solution
