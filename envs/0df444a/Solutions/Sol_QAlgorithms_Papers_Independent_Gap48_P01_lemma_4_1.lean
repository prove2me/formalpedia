-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P01.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:24:21.591759+00:00
-- url     : https://prove2.me/submissions/4f89d843-2fd5-4ffd-935e-db427a97f701

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01
noncomputable section

open scoped BigOperators Classical

open QAlgorithms.Papers.Independent.Gap48.P01

/-- Lemma 4.1, PDF p.24. Regular means multiplication has zero kernel;
no domain assumption and no assertion that the images are units is made. -/
theorem solution (S : Type*) [CommRing S] (a b : S)
    (ha : ∀ x : S, a*x = 0 → x = 0)
    (hb : ∀ x : S ⧸ Ideal.span ({a} : Set S),
      (Ideal.Quotient.mk (Ideal.span ({a} : Set S)) b) * x = 0 → x = 0) :
    ∀ x : S ⧸ Ideal.span ({b} : Set S),
      (Ideal.Quotient.mk (Ideal.span ({b} : Set S)) a) * x = 0 → x = 0 := by
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, hy⟩ := hx
  have h1 : Ideal.Quotient.mk (Ideal.span ({a} : Set S)) b *
      Ideal.Quotient.mk (Ideal.span ({a} : Set S)) y = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    exact ⟨x, by rw [mul_comm b y, hy, mul_comm]⟩
  have h2 := hb _ h1
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h2
  obtain ⟨z, rfl⟩ := h2
  have h3 : a * (x - b * z) = 0 := by
    linear_combination (-1 : S) * hy
  have h4 := ha _ h3
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨z, by linear_combination (-1 : S) * h4⟩

end
