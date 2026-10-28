-- Prove2me | solution 1 for QSVTPhaseEst.BitSearch.eq_B14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:56:05.421544+00:00
-- url     : https://prove2.me/submissions/c7500036-e5e6-4e6c-99e5-55f6704477d6

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

open QSVTPhaseEst.BitSearch in
theorem solution (Δ x : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 2 - Real.sqrt 2) (hx : |x| ≤ 1) :
    InDeltaRegion Δ |Real.cos (Real.pi * x)| ↔
      Real.pi * |x| ∈
        Set.Icc (Real.arccos (1 / Real.sqrt 2 + Δ / 2)) (Real.arccos (1 / Real.sqrt 2 - Δ / 2)) ∪
        Set.Icc (Real.arccos (-1 / Real.sqrt 2 + Δ / 2))
          (Real.arccos (-1 / Real.sqrt 2 - Δ / 2)) := by
  have hπ := Real.pi_pos
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    rw [div_eq_div_iff hs2.ne' two_ne_zero]; linarith
  have e : -1 / Real.sqrt 2 = -(Real.sqrt 2 / 2) := by rw [← hinv]; ring
  have hs2lt : Real.sqrt 2 < 2 := by nlinarith
  have hs2gt : 1 < Real.sqrt 2 := by nlinarith
  have ht : Real.pi * |x| = Real.arccos (Real.cos (Real.pi * x)) := by
    rw [← Real.cos_abs (Real.pi * x), abs_mul, abs_of_pos hπ,
      Real.arccos_cos (by positivity) (by nlinarith [abs_nonneg x])]
  rw [ht]
  set c := Real.cos (Real.pi * x) with hc
  have hc1 : c ∈ Set.Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have key : ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      (Real.arccos y ≤ Real.arccos c ↔ c ≤ y) ∧ (Real.arccos c ≤ Real.arccos y ↔ y ≤ c) :=
    fun y hy => ⟨Real.strictAntiOn_arccos.le_iff_ge hy hc1,
      Real.strictAntiOn_arccos.le_iff_ge hc1 hy⟩
  have m1 : 1 / Real.sqrt 2 + Δ / 2 ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have m2 : 1 / Real.sqrt 2 - Δ / 2 ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have m3 : -1 / Real.sqrt 2 + Δ / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [e]; exact ⟨by linarith, by linarith⟩
  have m4 : -1 / Real.sqrt 2 - Δ / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [e]; exact ⟨by linarith, by linarith⟩
  simp only [Set.mem_union, Set.mem_Icc]
  rw [(key _ m1).1, (key _ m2).2, (key _ m3).1, (key _ m4).2]
  unfold InDeltaRegion
  rw [e, hinv]
  have hapos : 0 < Real.sqrt 2 / 2 - Δ / 2 := by linarith
  rcases le_total 0 c with h0 | h0
  · rw [abs_of_nonneg h0]
    constructor
    · rintro ⟨h1, h2⟩; left; constructor <;> linarith
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · constructor <;> linarith
      · exfalso; linarith
  · rw [abs_of_nonpos h0]
    constructor
    · rintro ⟨h1, h2⟩; right; constructor <;> linarith
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exfalso; linarith
      · constructor <;> linarith
