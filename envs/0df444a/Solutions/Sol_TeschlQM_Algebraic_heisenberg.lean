-- Prove2me | solution 1 for TeschlQM.Algebraic.heisenberg
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T19:56:20.102153+00:00
-- url     : https://prove2.me/submissions/14df81e0-81d0-4202-a887-7dba96c97707

import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Algebraic_expectation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped InnerProductSpace
open TeschlQM.Algebraic

private theorem centered_uncertainty {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (u v : H) :
    1 / 2 * ‖⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ ∧
    ((∃ lam : ℝ, lam ≠ 0 ∧ v = (Complex.I * lam) • u) ∨ u = 0 ∨ v = 0 →
      ‖u‖ * ‖v‖ = 1 / 2 * ‖⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ‖) := by
  constructor
  · have htri := norm_sub_le (⟪u, v⟫_ℂ) (⟪v, u⟫_ℂ)
    have h1 := norm_inner_le_norm (𝕜 := ℂ) u v
    have h2 := norm_inner_le_norm (𝕜 := ℂ) v u
    nlinarith
  · rintro (⟨lam, hlam, hv⟩ | hu | hv)
    · have hz : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ =
          (2 * Complex.I * (lam : ℂ)) * ((‖u‖ ^ 2 : ℝ) : ℂ) := by
        rw [hv, inner_smul_right, inner_smul_left, inner_self_eq_norm_sq_to_K]
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
        simp only [RCLike.ofReal_eq_complex_ofReal]
        push_cast
        ring
      rw [hz, hv]
      simp [norm_smul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, pow_two]
      ring
    · simp [hu]
    · simp [hv]

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (hB : TeschlQM.Shared.IsSymmetric B)
    (ψ : H) (hψ : ‖ψ‖ = 1) (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain)
    (hAB : B ⟨ψ, hψB⟩ ∈ A.domain) (hBA : A ⟨ψ, hψA⟩ ∈ B.domain) :
    deviation A ⟨ψ, hψA⟩ * deviation B ⟨ψ, hψB⟩ ≥
        1 / 2 * ‖⟪ψ, A ⟨B ⟨ψ, hψB⟩, hAB⟩ - B ⟨A ⟨ψ, hψA⟩, hBA⟩⟫_ℂ‖ ∧
      ((∃ lam : ℝ, lam ≠ 0 ∧
          B ⟨ψ, hψB⟩ - expectation B ⟨ψ, hψB⟩ • ψ =
            (Complex.I * lam) • (A ⟨ψ, hψA⟩ - expectation A ⟨ψ, hψA⟩ • ψ)) ∨
        (∃ a : ℂ, A ⟨ψ, hψA⟩ = a • ψ) ∨ (∃ b : ℂ, B ⟨ψ, hψB⟩ = b • ψ) →
        deviation A ⟨ψ, hψA⟩ * deviation B ⟨ψ, hψB⟩ =
          1 / 2 * ‖⟪ψ, A ⟨B ⟨ψ, hψB⟩, hAB⟩ - B ⟨A ⟨ψ, hψA⟩, hBA⟩⟫_ℂ‖) := by
  let a := expectation A ⟨ψ, hψA⟩
  let b := expectation B ⟨ψ, hψB⟩
  let u := A ⟨ψ, hψA⟩ - a • ψ
  let v := B ⟨ψ, hψB⟩ - b • ψ
  have hψinner : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  have ha : starRingEnd ℂ a = a := by
    change starRingEnd ℂ (⟪ψ, A ⟨ψ, hψA⟩⟫_ℂ) = ⟪ψ, A ⟨ψ, hψA⟩⟫_ℂ
    rw [inner_conj_symm]
    exact (hA.2 ⟨ψ, hψA⟩ ⟨ψ, hψA⟩).symm
  have hb : starRingEnd ℂ b = b := by
    change starRingEnd ℂ (⟪ψ, B ⟨ψ, hψB⟩⟫_ℂ) = ⟪ψ, B ⟨ψ, hψB⟩⟫_ℂ
    rw [inner_conj_symm]
    exact (hB.2 ⟨ψ, hψB⟩ ⟨ψ, hψB⟩).symm
  have hAψ : ⟪A ⟨ψ, hψA⟩, ψ⟫_ℂ = a :=
    (hA.2 ⟨ψ, hψA⟩ ⟨ψ, hψA⟩).symm
  have hBψ : ⟪B ⟨ψ, hψB⟩, ψ⟫_ℂ = b :=
    (hB.2 ⟨ψ, hψB⟩ ⟨ψ, hψB⟩).symm
  have hψA' : ⟪ψ, A ⟨ψ, hψA⟩⟫_ℂ = a := rfl
  have hψB' : ⟪ψ, B ⟨ψ, hψB⟩⟫_ℂ = b := rfl
  have hcomm : ⟪ψ, A ⟨B ⟨ψ, hψB⟩, hAB⟩ - B ⟨A ⟨ψ, hψA⟩, hBA⟩⟫_ℂ =
      ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ := by
    rw [inner_sub_right, hA.2 ⟨ψ, hψA⟩ ⟨B ⟨ψ, hψB⟩, hAB⟩,
      hB.2 ⟨ψ, hψB⟩ ⟨A ⟨ψ, hψA⟩, hBA⟩]
    dsimp [u, v]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hψinner, ha, hb, hAψ, hBψ, hψA', hψB']
    ring
  rw [hcomm]
  change 1 / 2 * ‖⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ ∧ _
  refine ⟨(centered_uncertainty u v).1, ?_⟩
  intro hor
  apply (centered_uncertainty u v).2
  rcases hor with ⟨lam, hlam, heq⟩ | ⟨aa, heq⟩ | ⟨bb, heq⟩
  · exact Or.inl ⟨lam, hlam, heq⟩
  · right
    left
    have hea : a = aa := by
      dsimp [a, expectation]
      rw [heq, inner_smul_right, hψinner, mul_one]
    simp [u, heq, hea]
  · right
    right
    have heb : b = bb := by
      dsimp [b, expectation]
      rw [heq, inner_smul_right, hψinner, mul_one]
    simp [v, heq, heb]
