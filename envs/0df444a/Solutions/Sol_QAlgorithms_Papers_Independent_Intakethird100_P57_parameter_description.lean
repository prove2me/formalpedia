-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P57.parameter_description
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T08:06:53.206778+00:00
-- url     : https://prove2.me/submissions/a1e4cf41-3e55-49f2-9302-23e615618d67

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

namespace Aux_P57pd
open QAlgorithms.Papers.Independent.Intakethird100.P57

theorem pairs (N : ℕ) : Fintype.card {p : Fin N × Fin N // p.1 < p.2} = N * (N - 1) / 2 := by
  let e : {p : Fin N × Fin N // p.1 < p.2} ≃ Σ j : Fin N, Fin j.val :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
      invFun := fun s => ⟨(⟨s.2.val, s.2.isLt.trans s.1.isLt⟩, s.1), s.2.isLt⟩
      left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl
      right_inv := by rintro ⟨j, i⟩; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j => j) N, Finset.sum_range_id]

theorem graph_ext {N : ℕ} (G H : PhaseGraph N) (h : G.weight = H.weight) : G = H := by
  cases G; cases H
  simp only at h
  subst h
  rfl

end Aux_P57pd

open QAlgorithms.Papers.Independent.Intakethird100.P57 in
theorem solution :
    (∀ (N D : ℕ), 1 ≤ N → 1 ≤ D → Function.Injective (@describe N D)) ∧
    (∀ (N D : ℕ), 1 ≤ N → 1 ≤ D → Fintype.card (DescriptionIndex N D) =
      4 * N * D ^ 2 + N * (N - 1) / 2 + 8 * N) ∧
    (∃ C : ℕ, 0 < C ∧ ∀ N D : ℕ, 1 ≤ N → 1 ≤ D →
      Fintype.card (DescriptionIndex N D) ≤ C * (N * D ^ 2 + N ^ 2)) := by
  have hcard : ∀ (N D : ℕ), Fintype.card (DescriptionIndex N D) =
      4 * N * D ^ 2 + N * (N - 1) / 2 + 8 * N := by
    intro N D
    simp only [DescriptionIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, Aux_P57pd.pairs]
    generalize N * (N - 1) / 2 = K
    ring
  refine ⟨?_, fun N D _ _ => hcard N D, ⟨12, by norm_num, fun N D _ hD => ?_⟩⟩
  · intro N D _ _
    rintro ⟨t1, g1, r1⟩ ⟨t2, g2, r2⟩ h
    have ht : t1 = t2 := by
      funext k b i j
      apply Complex.ext
      · have := congrFun h (Sum.inl (k, b, i, j, false) : DescriptionIndex N D)
        simpa [describe] using this
      · have := congrFun h (Sum.inl (k, b, i, j, true) : DescriptionIndex N D)
        simpa [describe] using this
    have hg : g1 = g2 := by
      apply Aux_P57pd.graph_ext
      funext i j
      rcases lt_trichotomy i j with hij | rfl | hij
      · have := congrFun h (Sum.inr (Sum.inl ⟨(i, j), hij⟩) : DescriptionIndex N D)
        simpa [describe] using this
      · rw [g1.diagonal, g2.diagonal]
      · have := congrFun h (Sum.inr (Sum.inl ⟨(j, i), hij⟩) : DescriptionIndex N D)
        simp only [describe] at this
        rw [g1.symmetric, g2.symmetric]
        exact this
    have hr : r1 = r2 := by
      funext k
      apply Subtype.ext
      ext b c
      apply Complex.ext
      · have := congrFun h (Sum.inr (Sum.inr (k, b, c, false)) : DescriptionIndex N D)
        simpa [describe] using this
      · have := congrFun h (Sum.inr (Sum.inr (k, b, c, true)) : DescriptionIndex N D)
        simpa [describe] using this
    subst ht hg hr
    rfl
  · rw [hcard]
    have h1 : N * (N - 1) / 2 ≤ N ^ 2 :=
      (Nat.div_le_self _ _).trans (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have h2 : N ≤ N * D ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    nlinarith [h1, h2]

end
