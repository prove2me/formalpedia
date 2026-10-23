-- Prove2me | solution 1 for SOSInference.Means.eq_27
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T06:10:07.581306+00:00
-- url     : https://prove2.me/submissions/a0f55871-152b-4dab-afba-5100f6a0beb4

import Mathlib
import Definitions.Def_SOSInference_Means_sos
import Theorems.Thm_SOSInference_Means_eq_22

open SOSInference.Means
open scoped RealInnerProductSpace

theorem solution {l n : ℕ} {ι : Type*} [Fintype ι] (hn : 0 < n) (x : Fin n → E l) (z : ι → E l)
    (hx : ∀ i, ∃ j, z j = x i) (hother : ∀ i, ∃ j, z j ≠ x i)
    (hfeas : ∃ cpl, IsFeasibleCoupling (n := n) z 0 cpl) :
    IsGreatest
      (Set.range fun lam : E l =>
        -2 * ⟪lam, xbar x⟫ - (1 / (n : ℝ)) * ∑ i,
          max (‖lam‖ ^ 2 - ⨅ j : {j : ι // z j ≠ x i}, ‖z j - (x i + lam)‖ ^ 2) 0)
      (sos x z 0) := by
  classical
  obtain ⟨⟨lam0, γ0, hγ0, hcon0, hval0⟩, hub⟩ := eq_22 hn x z hx hfeas
  set D : Fin n → E l → ℝ := fun i lam => ⨅ j : {j : ι // z j ≠ x i}, ‖z j - (x i + lam)‖ ^ 2
    with hD
  have hsq : ∀ (lam : E l) i j, -⟪(2 : ℝ) • lam, z j⟫ + ‖x i - z j‖ ^ 2 =
      ‖z j - (x i + lam)‖ ^ 2 - (‖lam‖ ^ 2 + 2 * ⟪lam, x i⟫) := by
    intro lam i j
    have h1 : z j - (x i + lam) = (z j - x i) - lam := by abel
    rw [h1, norm_sub_sq_real (z j - x i) lam, norm_sub_sq_real (x i) (z j),
      norm_sub_sq_real (z j) (x i)]
    simp only [inner_smul_left, conj_trivial, inner_sub_left]
    linarith [real_inner_comm (x i) (z j), real_inner_comm lam (z j), real_inner_comm lam (x i)]
  have key : ∀ (lam : E l) i, (⨅ j, (-⟪(2 : ℝ) • lam, z j⟫ + ‖x i - z j‖ ^ 2)) =
      -2 * ⟪lam, x i⟫ - max (‖lam‖ ^ 2 - D i lam) 0 := by
    intro lam i
    have hne : Nonempty {j : ι // z j ≠ x i} := let ⟨j, hj⟩ := hother i; ⟨⟨j, hj⟩⟩
    have hιne : Nonempty ι := let ⟨j, _⟩ := hx i; ⟨j⟩
    have hmax : max (‖lam‖ ^ 2 - D i lam) 0 = ‖lam‖ ^ 2 - min (‖lam‖ ^ 2) (D i lam) := by
      rcases le_total (‖lam‖ ^ 2) (D i lam) with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]
    rw [hmax]
    simp only [hsq]
    apply le_antisymm
    · obtain ⟨j0, hj0⟩ := hx i
      have hle0 := ciInf_le (Finite.bddBelow_range
        (fun j => ‖z j - (x i + lam)‖ ^ 2 - (‖lam‖ ^ 2 + 2 * ⟪lam, x i⟫))) j0
      have hQ0 : ‖z j0 - (x i + lam)‖ ^ 2 = ‖lam‖ ^ 2 := by
        rw [hj0, show x i - (x i + lam) = -lam by abel, norm_neg]
      have hleD : (⨅ j, (‖z j - (x i + lam)‖ ^ 2 - (‖lam‖ ^ 2 + 2 * ⟪lam, x i⟫))) +
          (‖lam‖ ^ 2 + 2 * ⟪lam, x i⟫) ≤ D i lam := by
        apply le_ciInf
        intro j
        have := ciInf_le (Finite.bddBelow_range
          (fun j => ‖z j - (x i + lam)‖ ^ 2 - (‖lam‖ ^ 2 + 2 * ⟪lam, x i⟫))) (j : ι)
        linarith
      rcases min_choice (‖lam‖ ^ 2) (D i lam) with h | h <;> rw [h] <;> linarith
    · apply le_ciInf
      intro j
      by_cases hj : z j = x i
      · have hQ : ‖z j - (x i + lam)‖ ^ 2 = ‖lam‖ ^ 2 := by
          rw [hj, show x i - (x i + lam) = -lam by abel, norm_neg]
        have := min_le_left (‖lam‖ ^ 2) (D i lam)
        linarith
      · have hDle : D i lam ≤ ‖z j - (x i + lam)‖ ^ 2 :=
          ciInf_le (Finite.bddBelow_range (fun j : {j : ι // z j ≠ x i} =>
            ‖z j - (x i + lam)‖ ^ 2)) ⟨j, hj⟩
        have := min_le_right (‖lam‖ ^ 2) (D i lam)
        linarith
  have hx2 : ∀ lam : E l, ⟪(2 : ℝ) • lam, xbar x⟫ = 2 * ⟪lam, xbar x⟫ := by
    intro lam; rw [inner_smul_left]; simp
  -- every value of the objective is a dual value
  have hdual : ∀ lam : E l,
      -2 * ⟪lam, xbar x⟫ - (1 / (n : ℝ)) * ∑ i, max (‖lam‖ ^ 2 - D i lam) 0 ≤ sos x z 0 := by
    intro lam
    apply hub
    refine ⟨(2 : ℝ) • lam, fun i => max (‖lam‖ ^ 2 - D i lam) 0, fun i => le_max_right _ _,
      fun i => ?_, ?_⟩
    · rw [key]; simp only [inner_smul_left]; simp
    · rw [hx2]; ring
  refine ⟨⟨(1 / 2 : ℝ) • lam0, le_antisymm (hdual _) ?_⟩, ?_⟩
  · have h2 : (2 : ℝ) • ((1 / 2 : ℝ) • lam0) = lam0 := by
      rw [smul_smul]; norm_num
    have hγ : ∀ i, max (‖(1 / 2 : ℝ) • lam0‖ ^ 2 - D i ((1 / 2 : ℝ) • lam0)) 0 ≤ γ0 i := by
      intro i
      have := hcon0 i
      have hk := key ((1 / 2 : ℝ) • lam0) i
      rw [h2] at hk
      rw [hk] at this
      have e : ⟪lam0, x i⟫ = 2 * ⟪(1 / 2 : ℝ) • lam0, x i⟫ := by
        rw [inner_smul_left]; simp
      linarith
    rw [hval0]
    have e : ⟪lam0, xbar x⟫ = 2 * ⟪(1 / 2 : ℝ) • lam0, xbar x⟫ := by
      rw [inner_smul_left]; simp
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hγ i
    have hn' : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hs hn'
    simp only [hD] at this ⊢
    linarith
  · rintro _ ⟨lam, rfl⟩
    exact hdual lam
