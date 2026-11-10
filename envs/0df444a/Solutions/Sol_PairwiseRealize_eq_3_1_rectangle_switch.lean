-- Prove2me | solution 1 for PairwiseRealize.eq_3_1_rectangle_switch
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:11:07.056914+00:00
-- url     : https://prove2.me/submissions/cc74da60-d1b3-45c5-81d8-e343f11f061c

import Mathlib
import Definitions.Def_PairwiseRealize_Model

open PairwiseRealize in
theorem solution (n : ℕ) (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (x₁ x₂ : Row n) (hout : ∀ i, i ∉ A ∪ B → x₁ i = x₂ i) :
    let y₁ : Row n := fun i => if i ∈ B then x₂ i else x₁ i
    let y₂ : Row n := fun i => if i ∈ B then x₁ i else x₂ i
    let Δ : Feat n → ℤ := fun f => wvec n x₁ f + wvec n x₂ f - wvec n y₁ f - wvec n y₂ f
    Δ Feat.total = 0 ∧ (∀ i, Δ (Feat.single i) = 0) ∧
      ∀ i j (h : i < j), Δ (Feat.pair i j h) =
        if (i ∈ A ∧ j ∈ B) ∨ (i ∈ B ∧ j ∈ A) then
          (bv (x₁ i) - bv (x₂ i)) * (bv (x₁ j) - bv (x₂ j))
        else 0 := by
  intro y₁ y₂ Δ
  have hd : ∀ k, k ∈ A → k ∉ B := fun k hk hkB => Finset.disjoint_left.mp hAB hk hkB
  refine ⟨?_, ?_, ?_⟩
  · simp [Δ, wvec]
  · intro i
    by_cases hiB : i ∈ B <;> simp [Δ, wvec, y₁, y₂, hiB] <;> ring
  · intro i j h
    by_cases hiB : i ∈ B <;> by_cases hjB : j ∈ B <;> by_cases hiA : i ∈ A <;>
      by_cases hjA : j ∈ A <;>
      first
        | exact absurd hiB (hd i hiA)
        | exact absurd hjB (hd j hjA)
        | (have hi : x₁ i = x₂ i := by exact hout i (Finset.notMem_union.mpr ⟨hiA, hiB⟩)
           have hj : x₁ j = x₂ j := by exact hout j (Finset.notMem_union.mpr ⟨hjA, hjB⟩)
           simp [Δ, wvec, y₁, y₂, hiB, hjB, hiA, hjA, hi, hj] <;> ring1)
        | (have hi : x₁ i = x₂ i := by exact hout i (Finset.notMem_union.mpr ⟨hiA, hiB⟩)
           simp [Δ, wvec, y₁, y₂, hiB, hjB, hiA, hjA, hi] <;> ring1)
        | (have hj : x₁ j = x₂ j := by exact hout j (Finset.notMem_union.mpr ⟨hjA, hjB⟩)
           simp [Δ, wvec, y₁, y₂, hiB, hjB, hiA, hjA, hj] <;> ring1)
        | (simp [Δ, wvec, y₁, y₂, hiB, hjB, hiA, hjA] <;> ring1)
