-- Prove2me | solution 1 for ProxBundle.GPB.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:46:28.775458+00:00
-- url     : https://prove2.me/submissions/a2780704-3899-426c-992e-4091fc577159

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

open ProxBundle.GPB
open scoped InnerProductSpace RealInnerProductSpace

theorem solution {n : ℕ} (P : Instance n) (μ M L : ℝ)
    (hμ : 0 ≤ μ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hA1 : P.A1 μ) (hA3 : P.A3 M L) :
    ∀ x ∈ P.D, ∀ y ∈ P.D,
      P.f x - P.ellf x y ≤ 2 * M * ‖x - y‖ + L / 2 * ‖x - y‖ ^ 2 := by
  intro x hx y hy
  obtain ⟨-, hfconv, -, hsub⟩ := hA1
  have hDc : Convex ℝ P.D := hfconv.1
  have hN : ∀ N : ℕ, 0 < N → P.f x - P.f y - ⟪P.f' y, x - y⟫ ≤
      2 * M * ‖x - y‖ + L / 2 * ‖x - y‖ ^ 2 + L * ‖x - y‖ ^ 2 / (2 * N) := by
    intro N hN
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    set d := x - y with hd
    set c := ⟪P.f' y, d⟫ with hc
    let z : ℕ → E n := fun i => y + ((i:ℝ) / N) • d
    have hzD : ∀ i, i ≤ N → z i ∈ P.D := by
      intro i hi
      apply hDc.add_smul_sub_mem hy hx
      constructor
      · positivity
      · rw [div_le_one hNr]; exact_mod_cast hi
    have hstep : ∀ i, i < N → P.f (z (i+1)) - P.f (z i) ≤
        (1 / N) * c + (1 / N) * (2 * M + L * (((i:ℝ) + 1) / N) * ‖d‖) * ‖d‖ := by
      intro i hi
      have h1 := hsub (z (i+1)) (hzD _ hi) (z i) (hzD _ hi.le)
      unfold Instance.ellf at h1
      have hdiff : z i - z (i+1) = (-(1 / (N:ℝ))) • d := by
        simp only [z]
        rw [add_sub_add_left_eq_sub, ← sub_smul]
        congr 1
        push_cast
        field_simp
        ring
      have hzy : z (i+1) - y = (((i:ℝ) + 1) / N) • d := by
        simp only [z]; push_cast; abel
      rw [hdiff, real_inner_smul_right] at h1
      have h2 : ⟪P.f' (z (i+1)), d⟫ = c + ⟪P.f' (z (i+1)) - P.f' y, d⟫ := by
        rw [inner_sub_left]; ring
      have h3 : ⟪P.f' (z (i+1)) - P.f' y, d⟫ ≤ ‖P.f' (z (i+1)) - P.f' y‖ * ‖d‖ :=
        real_inner_le_norm _ _
      have h4 : ‖P.f' (z (i+1)) - P.f' y‖ ≤ 2 * M + L * ‖z (i+1) - y‖ :=
        hA3 _ (hzD _ hi) _ hy
      have h5 : ‖z (i+1) - y‖ = ((i:ℝ) + 1) / N * ‖d‖ := by
        rw [hzy, norm_smul, Real.norm_of_nonneg (by positivity)]
      rw [h5] at h4
      have h6 : ‖P.f' (z (i+1)) - P.f' y‖ * ‖d‖ ≤
          (2 * M + L * (((i:ℝ) + 1) / N * ‖d‖)) * ‖d‖ :=
        mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
      have h7 : (1 / (N:ℝ)) * ⟪P.f' (z (i+1)), d⟫ ≤
          (1 / N) * c + (1 / N) * (2 * M + L * (((i:ℝ) + 1) / N) * ‖d‖) * ‖d‖ := by
        rw [h2, mul_add, mul_assoc (1 / (N:ℝ)) (2 * M + _ ) ‖d‖]
        have : (2 * M + L * (((i:ℝ) + 1) / N) * ‖d‖) * ‖d‖ =
            (2 * M + L * (((i:ℝ) + 1) / N * ‖d‖)) * ‖d‖ := by ring
        rw [this]
        have := mul_le_mul_of_nonneg_left (h3.trans h6) (show (0:ℝ) ≤ 1 / N by positivity)
        linarith
      linarith
    have hind : ∀ i, i ≤ N → P.f (z i) - P.f y - ((i:ℝ) / N) * c ≤
        (i:ℝ) / N * (2 * M * ‖d‖) + L * ‖d‖ ^ 2 * ((i:ℝ) * ((i:ℝ) + 1)) / (2 * (N:ℝ) ^ 2) := by
      intro i
      induction i with
      | zero =>
        intro _
        simp [z]
      | succ i ih =>
        intro hi
        have h1 := ih (by omega)
        have h2 := hstep i (by omega)
        have e : ((((i + 1 : ℕ) : ℝ)) * (((i + 1 : ℕ) : ℝ) + 1)) =
            (i:ℝ) * ((i:ℝ) + 1) + 2 * ((i:ℝ) + 1) := by push_cast; ring
        rw [e]
        have e2 : L * ‖d‖ ^ 2 * ((i:ℝ) * ((i:ℝ) + 1) + 2 * ((i:ℝ) + 1)) / (2 * (N:ℝ) ^ 2) =
            L * ‖d‖ ^ 2 * ((i:ℝ) * ((i:ℝ) + 1)) / (2 * (N:ℝ) ^ 2) +
              (1 / N) * (L * (((i:ℝ) + 1) / N) * ‖d‖) * ‖d‖ := by
          field_simp
        rw [e2]
        have e3 : (((i + 1 : ℕ) : ℝ)) / N * c = (i:ℝ) / N * c + (1 / N) * c := by
          push_cast; field_simp
        have e4 : (((i + 1 : ℕ) : ℝ)) / N * (2 * M * ‖d‖) =
            (i:ℝ) / N * (2 * M * ‖d‖) + (1 / N) * (2 * M) * ‖d‖ := by
          push_cast; field_simp
        rw [e3, e4]
        have e5 : (1 / (N:ℝ)) * (2 * M + L * (((i:ℝ) + 1) / N) * ‖d‖) * ‖d‖ =
            (1 / N) * (2 * M) * ‖d‖ + (1 / N) * (L * (((i:ℝ) + 1) / N) * ‖d‖) * ‖d‖ := by
          ring
        rw [e5] at h2
        linarith
    have hzN : z N = x := by
      simp only [z, d]
      rw [div_self hNr.ne', one_smul]; abel
    have := hind N le_rfl
    rw [hzN, div_self hNr.ne', one_mul, one_mul] at this
    have e6 : L * ‖d‖ ^ 2 * ((N:ℝ) * ((N:ℝ) + 1)) / (2 * (N:ℝ) ^ 2) =
        L / 2 * ‖d‖ ^ 2 + L * ‖d‖ ^ 2 / (2 * N) := by
      field_simp
    rw [e6] at this
    linarith
  unfold Instance.ellf
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨N, hNgt⟩ := exists_nat_gt (L * ‖x - y‖ ^ 2 / (2 * δ))
  have hN0 : 0 < N := by
    have : (0:ℝ) < N := lt_of_le_of_lt (by positivity) hNgt
    exact_mod_cast this
  have hNr : (0:ℝ) < N := by exact_mod_cast hN0
  have h1 := hN N hN0
  have h2 : L * ‖x - y‖ ^ 2 / (2 * N) ≤ δ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hNgt
    nlinarith
  linarith
