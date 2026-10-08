-- Prove2me | solution 1 for RiskUncSets.InnerApprox.mix_mem_restrictedSimplex_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:19:45.743587+00:00
-- url     : https://prove2.me/submissions/07d0b551-d2e7-4c9f-b244-8fcb91f5216c

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting

set_option autoImplicit false

noncomputable section

open RiskUncSets.InnerApprox in
theorem solution {N : ℕ} (hN : 0 < N) (qh : Fin N → ℝ)
    (hqh : qh ∈ restrictedSimplex N) (hmin : (N : ℝ) * (⨅ i, qh i) < 1)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    mix qh lam ∈ restrictedSimplex N ↔ lam ≤ 1 / (1 - (N : ℝ) * ⨅ i, qh i) := by
  obtain ⟨⟨hnn, hsum⟩, hanti⟩ := hqh
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set m := ⨅ i, qh i with hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < 1 - (N : ℝ) * m := by linarith
  have hmle : ∀ i, m ≤ qh i := fun i => ciInf_le (Set.finite_range qh).bddBelow i
  obtain ⟨i0, hi0⟩ : ∃ i0, qh i0 = m := by
    obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := qh)
    exact ⟨i0, hi0⟩
  have key : lam ≤ 1 / (1 - (N : ℝ) * m) ↔ 0 ≤ lam * m + (1 - lam) * (1 / (N : ℝ)) := by
    rw [le_div_iff₀ hpos]
    have h1 : lam * m + (1 - lam) * (1 / (N : ℝ)) = (1 - lam * (1 - (N : ℝ) * m)) / N := by
      field_simp
      ring
    rw [h1, div_nonneg_iff]
    constructor
    · intro h; left; exact ⟨by linarith, hNpos.le⟩
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · linarith
      · linarith
  rw [key]
  constructor
  · rintro ⟨⟨hnn', _⟩, _⟩
    have := hnn' i0
    simp only [mix] at this
    rw [hi0] at this
    exact this
  · intro h
    refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
    · simp only [mix]
      have := hmle i
      nlinarith
    · simp only [mix]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    · intro i j hij
      simp only [mix]
      have := hanti hij
      nlinarith
