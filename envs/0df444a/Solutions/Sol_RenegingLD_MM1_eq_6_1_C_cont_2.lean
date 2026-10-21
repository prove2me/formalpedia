-- Prove2me | solution 2 for RenegingLD.MM1.eq_6_1_C_cont
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:41:51.97679+00:00
-- url     : https://prove2.me/submissions/b60a7eb1-f3bc-40a6-a831-7e644152da6b

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
open RenegingLD.MM1

lemma rld_sqrt_gt (lam mu γ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hγ : 0 ≤ γ) :
    γ < Real.sqrt (γ ^ 2 + 4 * lam * mu) := by
  apply Real.lt_sqrt_of_sq_lt
  nlinarith [mul_pos hlam hmu]

lemma rld_z_pos (lam mu γ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hγ : 0 ≤ γ) :
    0 < z lam mu γ := by
  unfold z
  have := rld_sqrt_gt lam mu γ hlam hmu hγ
  apply div_pos <;> linarith

lemma rld_z_eq (lam mu γ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hγ : 0 ≤ γ) :
    mu * (z lam mu γ) ^ 2 + γ * z lam mu γ = lam := by
  have hs : Real.sqrt (γ ^ 2 + 4 * lam * mu) ^ 2 = γ ^ 2 + 4 * lam * mu :=
    Real.sq_sqrt (by nlinarith [mul_pos hlam hmu])
  have h2 : 2 * mu * z lam mu γ = Real.sqrt (γ ^ 2 + 4 * lam * mu) - γ := by
    unfold z
    field_simp
  apply mul_left_cancel₀ (show (4 * mu : ℝ) ≠ 0 by positivity)
  have : (4 * mu) * (mu * z lam mu γ ^ 2 + γ * z lam mu γ)
      = (2 * mu * z lam mu γ) ^ 2 + 2 * γ * (2 * mu * z lam mu γ) := by ring
  rw [this, h2]
  nlinarith [hs]

lemma rld_z_cont (lam mu : ℝ) : Continuous (z lam mu) := by
  unfold z
  fun_prop

theorem solution (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hlm : mu ≤ lam) :
    (∀ γ : ℝ, 0 ≤ γ →
      0 < z lam mu γ ∧ lam * (z lam mu γ)⁻¹ - mu * z lam mu γ - γ = 0 ∧
        ∀ w : ℝ, 0 < w → lam * w⁻¹ - mu * w - γ = 0 → w = z lam mu γ) ∧
    ContinuousOn (C lam mu) (Set.Ici 0) ∧
    C lam mu (lam - mu) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ
    have hz := rld_z_pos lam mu γ hlam hmu hγ
    have he := rld_z_eq lam mu γ hlam hmu hγ
    refine ⟨hz, ?_, ?_⟩
    · field_simp
      nlinarith [he]
    · intro w hw hw2
      have h1 : mu * w ^ 2 + γ * w = lam := by
        field_simp at hw2
        nlinarith [hw2]
      have h2 : (w - z lam mu γ) * (mu * (w + z lam mu γ) + γ) = 0 := by
        nlinarith [h1, he]
      have h3 : mu * (w + z lam mu γ) + γ ≠ 0 := by
        have : 0 < mu * (w + z lam mu γ) + γ := by positivity
        exact this.ne'
      have := (mul_eq_zero.mp h2).resolve_right h3
      linarith
  · intro γ hγ
    have hz := rld_z_pos lam mu γ hlam hmu (by simpa using hγ)
    have hc := (rld_z_cont lam mu).continuousAt (x := γ)
    unfold C
    apply ContinuousAt.continuousWithinAt
    have hne : z lam mu γ ≠ 0 := hz.ne'
    fun_prop (disch := exact hne)
  · have hγ : (0:ℝ) ≤ lam - mu := by linarith
    have : z lam mu (lam - mu) = 1 := by
      unfold z
      have : Real.sqrt ((lam - mu) ^ 2 + 4 * lam * mu) = lam + mu := by
        rw [show (lam - mu) ^ 2 + 4 * lam * mu = (lam + mu) ^ 2 by ring]
        exact Real.sqrt_sq (by linarith)
      rw [this]
      field_simp
      ring
    unfold C
    rw [this]
    simp
