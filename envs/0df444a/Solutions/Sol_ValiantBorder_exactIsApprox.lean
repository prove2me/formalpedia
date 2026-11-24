-- Prove2me | solution 1 for ValiantBorder.exactIsApprox
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-23T23:57:55.641849+00:00
-- url     : https://prove2.me/submissions/efafe127-3902-4ce7-af45-86f48adc22fe

import Definitions.Def_VP_VNP_all_fields

/-! This proof uses the circuit and Laurent-series definitions in Anthropic's
`vp-vnp/Statement.lean` (Apache-2.0), released with *VP ≠ VNP over every field*.
The proof below is an independent argument for this elementary implication. -/

open MvPolynomial

universe u

/-- Every exact circuit gives a border approximation of the same size. -/
theorem solution {F : Type u} [Field F] {V : Type} (f : MvPolynomial V F) (s : ℕ)
    (h : Statement.Computes f s) : Statement.Approximates f s := by
  classical
  let embed : F →+* LaurentSeries F := HahnSeries.C
  obtain ⟨gates, valid, k, hk, output⟩ := h
  refine ⟨MvPolynomial.map embed f, ⟨fun j => MvPolynomial.map embed (gates j), ?_, ?_⟩, ?_⟩
  · intro j hj
    rcases valid j hj with ⟨v, hv⟩ | ⟨a, ha⟩ | ⟨i, hi, t, ht, hsum⟩ | ⟨i, hi, t, ht, hprod⟩
    · exact Or.inl ⟨v, by simp [hv]⟩
    · exact Or.inr (Or.inl ⟨embed a, by simp [ha]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, t, ht, by simp [hsum]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, t, ht, by simp [hprod]⟩))
  · exact ⟨k, hk, congrArg (MvPolynomial.map embed) output⟩
  · intro d i _
    rw [MvPolynomial.coeff_map]
    by_cases hi : i = 0 <;> simp [embed, HahnSeries.C_apply, hi]
