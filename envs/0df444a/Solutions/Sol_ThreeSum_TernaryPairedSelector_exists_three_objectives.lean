-- Prove2me | solution 1 for ThreeSum.TernaryPairedSelector.exists_three_objectives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:24.23828+00:00
-- url     : https://prove2.me/submissions/d9d72e2e-eafd-40bb-87da-d19e3386c593

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedSelector
open Finset
open scoped BigOperators
variable {Ω : Type*} [DecidableEq Ω]
namespace ThreeSum.TernaryPairedSelector
theorem _root_.solution (S : Finset Ω) (hS : S.Nonempty)
    (f : Fin 3 → Ω → ℚ) (normalizer : Fin 3 → ℚ)
    (hf : ∀ i seed, 0 ≤ f i seed) (hN : ∀ i, 0 ≤ normalizer i)
    (havg : ∀ i, (∑ seed ∈ S, f i seed) ≤ S.card*normalizer i) :
    ∃ seed ∈ S, ∀ i, f i seed ≤ 3*normalizer i := by
  let term := fun i seed => if normalizer i = 0 then 0 else f i seed / normalizer i
  have ht0 (i : Fin 3) (seed : Ω) : 0 ≤ term i seed := by
    dsimp [term]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (hf i seed) (hN i)
  have hsum (i : Fin 3) : (∑ seed ∈ S, term i seed) ≤ S.card := by
    by_cases hn : normalizer i = 0
    · simp [term,hn]
    · have hp : 0 < normalizer i := lt_of_le_of_ne (hN i) (Ne.symm hn)
      simpa [term,hn,← sum_div] using (div_le_iff₀ hp).mpr (havg i)
  have hscore : (∑ seed ∈ S, score f normalizer seed) ≤ ∑ _seed ∈ S, (3 : ℚ) := by
    unfold score
    rw [sum_comm]
    calc
      _ ≤ ∑ _i : Fin 3, (S.card : ℚ) := sum_le_sum fun i _ => hsum i
      _ = _ := by simp; ring
  obtain ⟨seed,hseed,hs⟩ := exists_le_of_sum_le hS hscore
  refine ⟨seed,hseed, ?_⟩
  intro i
  by_cases hn : normalizer i = 0
  · have hle : f i seed ≤ ∑ seed ∈ S, f i seed :=
      single_le_sum (fun a ha => hf i a) hseed
    have hh := havg i
    simp only [hn,mul_zero] at hh ⊢
    exact hle.trans hh
  · have hp : 0 < normalizer i := lt_of_le_of_ne (hN i) (Ne.symm hn)
    have ht : term i seed ≤ score f normalizer seed :=
      single_le_sum (fun j hj => ht0 j seed) (mem_univ i)
    have hh : f i seed / normalizer i ≤ 3 := by
      simpa [term,hn] using ht.trans hs
    exact (div_le_iff₀ hp).mp hh
end ThreeSum.TernaryPairedSelector
