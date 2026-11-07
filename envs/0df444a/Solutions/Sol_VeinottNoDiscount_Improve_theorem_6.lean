-- Prove2me | solution 1 for VeinottNoDiscount.Improve.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:13:36.050795+00:00
-- url     : https://prove2.me/submissions/617f9d8b-23ed-4cb6-b44c-b3ed98a02c7b

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
import Theorems.Thm_VeinottNoDiscount_Improve_theorem_5
import Theorems.Thm_VeinottNoDiscount_Improve_corollary_1
import Theorems.Thm_VeinottNoDiscount_Improve_lemma_4
import Theorems.Thm_VeinottNoDiscount_Improve_lemma_5
import Theorems.Thm_VeinottNoDiscount_Improve_proof_theorem_6b
import Theorems.Thm_VeinottNoDiscount_Improve_proof_theorem_6d
import Theorems.Thm_BlackwellDiscreteDP_NearOne_lemma_2
open Filter Topology Matrix BlackwellDiscreteDP.NearOne VeinottNoDiscount.Improve

theorem solution {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    (GSet M f = ∅ → f ∈ Fprime M) ∧
      (GSet M f ∪ HSet M f = ∅ → f ∈ Fdprime M) ∧
      (∀ g ∈ GSet M f, VecGt (M.x g) (M.x f) ∨ (M.x g = M.x f ∧ VecGt (M.y g) (M.y f))) ∧
      (∀ g ∈ HSet M f, M.x g = M.x f ∧
        (VecGt (M.y g) (M.y f) ∨ (M.y g = M.y f ∧ VecGt (z M g) (z M f)))) := by
  refine ⟨(VeinottNoDiscount.Improve.theorem_5 M f).1, fun hGH => ?_,
    fun g hg => VeinottNoDiscount.Improve.corollary_1 M f g hg, fun g hg => ?_⟩
  · have hG : GSet M f = ∅ := Set.subset_eq_empty Set.subset_union_left hGH
    have hH : HSet M f = ∅ := Set.subset_eq_empty Set.subset_union_right hGH
    exact VeinottNoDiscount.Improve.lemma_5 M f hG
      ((VeinottNoDiscount.Improve.proof_theorem_6b M f).2 hH)
  · have hgE : g ∈ ESet M f := hg.1
    refine ⟨(BlackwellDiscreteDP.NearOne.lemma_2 M f g hgE).1, ?_⟩
    have hy := (VeinottNoDiscount.Improve.lemma_4 M f g hgE).2
    obtain ⟨hw0, hd⟩ := VeinottNoDiscount.Improve.proof_theorem_6d M f g hg
    rcases hd with hd | ⟨he, hz⟩
    · left
      rw [hw0] at hd
      refine ⟨fun s => ?_, fun heq => hd.2 ?_⟩
      · rw [hy]; have := hd.1 s; simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; linarith
      · rw [hy] at heq
        funext s; have := congrFun heq s; simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
        linarith
    · right
      exact ⟨by rw [hy, he, hw0, add_zero], hz⟩
