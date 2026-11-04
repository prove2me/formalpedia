-- Prove2me | solution 1 for ThreeSum.TernaryCoverPairStep.pair_step_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:48.002314+00:00
-- url     : https://prove2.me/submissions/f4456049-bab7-44ea-b29a-b17aa2f199dc

import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
import Theorems.Thm_ThreeSum_TernaryCoverPairStep_pairedSet_prior
import Theorems.Thm_ThreeSum_TernaryCoverRankFibers_affineFiber_card_le_pow_finrank


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverPairStep
open Finset TernaryCoverRankFibers
variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
variable {E Z ι : Type*} [Fintype E] [Fintype Z] [Fintype ι] [DecidableEq K]
namespace ThreeSum.TernaryCoverPairStep
theorem _root_.solution (left right : E → ι → K) (prior : Z → ι → X) (P : ℕ)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hE : Fintype.card E ≤ P ^ 2)
    (hprojection : ∀ β γ : K, (β ≠ 0 ∨ γ ≠ 0) → ∀ q : ι → K,
      (projectionFiber left right β γ q).card ≤ P)
    (S : Submodule K (X × (K × K))) :
    (pairedSet left right prior S).card ≤
      (priorSet prior S).card * P ^ Module.finrank K (vertical S) := by
  classical
  have hfiber (z : Z) :
      ((pairedSet left right prior S).filter fun ze => ze.1 = z).card ≤
        P ^ Module.finrank K (vertical S) := by
    let F := (pairedSet left right prior S).filter fun ze => ze.1 = z
    change F.card ≤ _
    by_cases hz : F.card = 0
    · rw [hz]
      exact Nat.zero_le _
    obtain ⟨ze0, hze0⟩ := card_pos.mp (Nat.pos_of_ne_zero hz)
    let offset : ι → K × K := fun i => (left ze0.2 i, right ze0.2 i)
    have hin : ∀ ze ∈ F, ze.2 ∈ affineFiber left right (vertical S) offset := by
      intro ze hze
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro i
      have hz0 := (mem_filter.mp hze0).2
      have hzz := (mem_filter.mp hze).2
      have ha := (mem_filter.mp (mem_filter.mp hze).1).2 i
      have hb := (mem_filter.mp (mem_filter.mp hze0).1).2 i
      have hh := S.sub_mem ha hb
      change (0, (left ze.2 i, right ze.2 i) - offset i) ∈ S
      change (prior ze.1 i - prior ze0.1 i,
        (left ze.2 i, right ze.2 i) - (left ze0.2 i, right ze0.2 i)) ∈ S at hh
      rw [hzz, hz0, sub_self] at hh
      exact hh
    have hi : F.card ≤ (affineFiber left right (vertical S) offset).card := by
      apply card_le_card_of_injOn Prod.snd hin
      intro a ha b hb heq
      exact Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) heq
    exact hi.trans (affineFiber_card_le_pow_finrank left right P hinj hE hprojection _ _)
  calc
    _ = ∑ z ∈ priorSet prior S,
        ((pairedSet left right prior S).filter fun ze => ze.1 = z).card :=
      card_eq_sum_card_fiberwise (fun ze hze => pairedSet_prior left right prior S hze)
    _ ≤ ∑ _z ∈ priorSet prior S, P ^ Module.finrank K (vertical S) :=
      sum_le_sum (fun z _ => hfiber z)
    _ = _ := by simp
end ThreeSum.TernaryCoverPairStep
