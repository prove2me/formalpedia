-- Prove2me | solution 1 for RoughgardenPOA.theorem_3_2_extension_static
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T15:10:02.889073+00:00
-- url     : https://prove2.me/submissions/9fc4e313-fabb-4922-bdc7-a2d767367f2f

import Mathlib
import Definitions.Def_RoughgardenPOA_objective
import Definitions.Def_RoughgardenPOA_robustPOA
import Definitions.Def_RoughgardenPOA_IsCCE

set_option autoImplicit false

namespace RoughgardenPOAAux

open MeasureTheory RoughgardenPOA

/-- Smoothness argument: for a CCE, `(1 - mu) * E ≤ lam * C(s*)`. -/
theorem cce_smooth_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (C : ι → (∀ i, S i) → ℝ) (σ : Measure (∀ i, S i)) (hσ : IsCCE C σ)
    (sStar : ∀ i, S i) (lam mu : ℝ) (hs : IsSmooth C lam mu) :
    (∫ s, objective C s ∂σ) ≤ lam * objective C sStar + mu * ∫ s, objective C s ∂σ := by
  obtain ⟨hP, hI, hIu, hle⟩ := hσ
  have hobjI : Integrable (fun s => objective C s) σ := by
    unfold objective
    exact integrable_finsetSum _ (fun i _ => hI i)
  have h1 : (∫ s, objective C s ∂σ) = ∑ i, ∫ s, C i s ∂σ := by
    unfold objective
    exact integral_finsetSum _ (fun i _ => hI i)
  have h2 : (∑ i, ∫ s, C i s ∂σ) ≤ ∑ i, ∫ s, C i (Function.update s i (sStar i)) ∂σ :=
    Finset.sum_le_sum (fun i _ => hle i (sStar i))
  have h3 : (∑ i, ∫ s, C i (Function.update s i (sStar i)) ∂σ)
      = ∫ s, ∑ i, C i (Function.update s i (sStar i)) ∂σ :=
    (integral_finsetSum _ (fun i _ => hIu i (sStar i))).symm
  have hRI : Integrable (fun s => lam * objective C sStar + mu * objective C s) σ :=
    (integrable_const _).add (hobjI.const_mul mu)
  have h4 : (∫ s, ∑ i, C i (Function.update s i (sStar i)) ∂σ)
      ≤ ∫ s, (lam * objective C sStar + mu * objective C s) ∂σ := by
    apply integral_mono (integrable_finsetSum _ (fun i _ => hIu i (sStar i))) hRI
    intro s
    exact hs s sStar
  have h5 : (∫ s, (lam * objective C sStar + mu * objective C s) ∂σ)
      = lam * objective C sStar + mu * ∫ s, objective C s ∂σ := by
    rw [integral_add (integrable_const _) (hobjI.const_mul mu), integral_const,
      integral_const_mul]
    simp
  linarith

theorem main
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (C : ι → (∀ i, S i) → ℝ) (σ : Measure (∀ i, S i)) (hσ : IsCCE C σ)
    (sStar : ∀ i, S i) (hρ : robustPOA C ≠ ⊤ ∨ 0 < objective C sStar) :
    ((∫ s, objective C s ∂σ : ℝ) : EReal) ≤ robustPOA C * ((objective C sStar : ℝ) : EReal) := by
  set E : ℝ := ∫ s, objective C s ∂σ with hE
  set c : ℝ := objective C sStar with hc
  -- per-pair bound: E * (1 - mu) ≤ lam * c
  have hpair : ∀ p : ℝ × ℝ, p.2 < 1 → IsSmooth C p.1 p.2 → E ≤ p.1 / (1 - p.2) * c := by
    intro p hp hs
    have hb := cce_smooth_bound C σ hσ sStar p.1 p.2 hs
    have hpos : 0 < 1 - p.2 := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith
  have hlb : ∀ p : ℝ × ℝ, p.2 < 1 ∧ IsSmooth C p.1 p.2 → robustPOA C ≤ ((p.1 / (1 - p.2) : ℝ) : EReal) := by
    intro p hp
    unfold robustPOA
    exact iInf₂_le p hp
  rcases lt_trichotomy 0 c with hcpos | hc0 | hcneg
  · -- c > 0
    have hge : ((E / c : ℝ) : EReal) ≤ robustPOA C := by
      unfold robustPOA
      refine le_iInf₂ (fun p hp => ?_)
      have := hpair p hp.1 hp.2
      exact EReal.coe_le_coe_iff.mpr ((div_le_iff₀ hcpos).mpr this)
    generalize robustPOA C = R at hge ⊢
    induction R using EReal.rec with
    | bot => exact absurd hge (by simp)
    | top => rw [EReal.top_mul_of_pos (EReal.coe_pos.mpr hcpos)]; exact le_top
    | coe r =>
      have hr : E / c ≤ r := EReal.coe_le_coe_iff.mp hge
      have : E ≤ r * c := (div_le_iff₀ hcpos).mp hr
      rw [← EReal.coe_mul]
      exact EReal.coe_le_coe_iff.mpr this
  · -- c = 0
    have hne : robustPOA C ≠ ⊤ := by
      rcases hρ with h | h
      · exact h
      · exact absurd h (by rw [← hc0]; exact lt_irrefl 0)
    have hex : ∃ p : ℝ × ℝ, p.2 < 1 ∧ IsSmooth C p.1 p.2 := by
      by_contra hn
      push_neg at hn
      apply hne
      unfold robustPOA
      refine iInf₂_eq_top.mpr ?_
      intro p hp
      exact absurd hp.2 (hn p hp.1)
    obtain ⟨p, hp⟩ := hex
    have := hpair p hp.1 hp.2
    rw [← hc0, mul_zero] at this
    rw [← hc0]
    simp only [EReal.coe_zero, mul_zero]
    exact EReal.coe_le_coe_iff.mpr (by simpa using this)
  · -- c < 0
    have hne : robustPOA C ≠ ⊤ := by
      rcases hρ with h | h
      · exact h
      · exact absurd h (not_lt.mpr hcneg.le)
    have hex : ∃ p : ℝ × ℝ, p.2 < 1 ∧ IsSmooth C p.1 p.2 := by
      by_contra hn
      push_neg at hn
      apply hne
      unfold robustPOA
      refine iInf₂_eq_top.mpr ?_
      intro p hp
      exact absurd hp.2 (hn p hp.1)
    obtain ⟨p, hp⟩ := hex
    have hq := hpair p hp.1 hp.2
    have hl := hlb p hp
    generalize robustPOA C = R at hl hne ⊢
    induction R using EReal.rec with
    | bot =>
      rw [EReal.bot_mul_of_neg (EReal.coe_neg'.mpr hcneg)]
      exact le_top
    | top => exact absurd rfl hne
    | coe r =>
      have hr : r ≤ p.1 / (1 - p.2) := EReal.coe_le_coe_iff.mp hl
      have : E ≤ r * c := le_trans hq (mul_le_mul_of_nonpos_right hr hcneg.le)
      rw [← EReal.coe_mul]
      exact EReal.coe_le_coe_iff.mpr this

end RoughgardenPOAAux

open RoughgardenPOA in
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (C : ι → (∀ i, S i) → ℝ) (σ : MeasureTheory.Measure (∀ i, S i)) (hσ : IsCCE C σ)
    (sStar : ∀ i, S i) (hρ : robustPOA C ≠ ⊤ ∨ 0 < objective C sStar) :
    ((∫ s, objective C s ∂σ : ℝ) : EReal) ≤ robustPOA C * ((objective C sStar : ℝ) : EReal) := by
  exact RoughgardenPOAAux.main C σ hσ sStar hρ
