-- Prove2me | solution 1 for SoftRobust.Duality.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T23:52:27.07934+00:00
-- url     : https://prove2.me/submissions/7b3e889c-537a-44eb-9d42-a9c6d9754c4f

import Mathlib
import Definitions.Def_SoftRobust_Duality_Mixture
import Definitions.Def_SoftRobust_Duality_ConvexRiskMeasure
import Definitions.Def_SoftRobust_Duality_Model
import Theorems.Thm_SoftRobust_Duality_inf_reparam
import Theorems.Thm_SoftRobust_Duality_strong_duality
import Theorems.Thm_SoftRobust_Duality_scaling_identity
import Theorems.Thm_SoftRobust_Duality_rhoQ_normalized_convex
import Theorems.Thm_SoftRobust_Duality_familyOfPenalty_props
import Theorems.Thm_SoftRobust_Duality_penaltyOfFamily_familyOfPenalty

open MeasureTheory
open scoped NNReal ENNReal

namespace SoftRobustT21Aux

open SoftRobust.Duality

variable {Ω : Type*} [MeasurableSpace Ω]

lemma bdd_payoff {n m : ℕ} (M : Model Ω n m) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ M.X) :
    IsBddPayoff (M.payoff x) :=
  ⟨M.payoff_measurable x hx, M.payoff_bounded x hx⟩

lemma bdd_div {Y : Ω → ℝ} (hY : IsBddPayoff Y) (c : ℝ) : IsBddPayoff (fun ω => Y ω / c) := by
  obtain ⟨hm, C, hC⟩ := hY
  refine ⟨hm.div_const c, C * |c|⁻¹, fun ω => ?_⟩
  rw [abs_div, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hC ω) (inv_nonneg.2 (abs_nonneg c))

/-- Part (a) for a single decision `x ∈ X`. -/
lemma partA_x {n m : ℕ} (M : Model Ω n m) (δ : ℝ) (hδ : 0 < δ)
    (𝒬 : ℝ≥0 → Set (ProbabilityMeasure Ω)) (h𝒬 : IsAdmissibleFamily 𝒬)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M.X) :
    (∃ l₀ ∈ Set.Ici (0 : ℝ), IsMinOn (dualObjective (rhoQ 𝒬) δ (M.payoff x)) (Set.Ici 0) l₀) ∧
    (x ∈ softRobustSet M 𝒬 δ ↔ ∃ l₀ ∈ Set.Ici (0 : ℝ),
      IsMinOn (dualObjective (rhoQ 𝒬) δ (M.payoff x)) (Set.Ici 0) l₀ ∧
        dualObjective (rhoQ 𝒬) δ (M.payoff x) l₀ ≤ 0) := by
  set D := dualObjective (rhoQ 𝒬) δ (M.payoff x) with hDdef
  have hF : ∀ l : ℝ, 0 ≤ l →
      ((-(l * δ) : ℝ) : EReal) +
          (⨅ Q : ProbabilityMeasure Ω,
            ((∫ ω, M.payoff x ω ∂(Q : Measure Ω) : ℝ) : EReal) +
              ((l + 1 : ℝ) : EReal) * (penaltyOfFamily 𝒬 Q : EReal)) = ((-(D l) : ℝ) : EReal) := by
    intro l hl
    rw [scaling_identity 𝒬 h𝒬 (M.payoff x) (bdd_payoff M hx) l hl, ← EReal.coe_add]
    congr 1
    simp only [hDdef, dualObjective]
    ring
  obtain ⟨⟨l₀, hl₀, hl₀P⟩, hub⟩ := strong_duality M 𝒬 h𝒬 δ hδ x hx
  simp only at hl₀P
  rw [hF l₀ hl₀] at hl₀P
  have hmin : IsMinOn D (Set.Ici 0) l₀ := by
    rw [isMinOn_iff]
    intro l hl
    have := hub ⟨l, hl, rfl⟩
    simp only at this
    rw [hF l hl, ← hl₀P] at this
    have := EReal.coe_le_coe_iff.1 this
    linarith
  refine ⟨⟨l₀, hl₀, hmin⟩, ?_⟩
  have hrep := inf_reparam M 𝒬 h𝒬 δ hδ x hx
  rw [← hl₀P] at hrep
  have key : x ∈ softRobustSet M 𝒬 δ ↔ D l₀ ≤ 0 := by
    have : x ∈ softRobustSet M 𝒬 δ ↔ (0 : EReal) ≤ ((-(D l₀) : ℝ) : EReal) := by
      rw [← hrep]
      simp only [le_iInf_iff, softRobustSet, Set.mem_setOf_eq]
      constructor
      · rintro ⟨-, h⟩ ε hε Q hQ
        have := h ε hε Q hQ
        exact_mod_cast (by linarith : (0 : ℝ) ≤ (∫ ω, M.payoff x ω ∂(Q : Measure Ω)) + ε)
      · intro h
        refine ⟨hx, fun ε hε Q hQ => ?_⟩
        have := h ε hε Q hQ
        have : (0 : ℝ) ≤ (∫ ω, M.payoff x ω ∂(Q : Measure Ω)) + ε := by exact_mod_cast this
        linarith
    rw [this, EReal.coe_nonneg]
    constructor <;> intro h <;> linarith
  rw [key]
  constructor
  · intro h
    exact ⟨l₀, hl₀, hmin, h⟩
  · rintro ⟨l₁, hl₁, -, h⟩
    exact (hmin hl₁).trans h

lemma partA {n m : ℕ} (M : Model Ω n m) (δ : ℝ) (hδ : 0 < δ)
    (𝒬 : ℝ≥0 → Set (ProbabilityMeasure Ω)) (h𝒬 : IsAdmissibleFamily 𝒬) :
    (∀ x ∈ M.X, ∃ l₀ ∈ Set.Ici (0 : ℝ),
          IsMinOn (dualObjective (rhoQ 𝒬) δ (M.payoff x)) (Set.Ici 0) l₀) ∧
        softRobustSet M 𝒬 δ =
          {x | x ∈ M.X ∧ ∃ l₀ ∈ Set.Ici (0 : ℝ),
            IsMinOn (dualObjective (rhoQ 𝒬) δ (M.payoff x)) (Set.Ici 0) l₀ ∧
              dualObjective (rhoQ 𝒬) δ (M.payoff x) l₀ ≤ 0} := by
  refine ⟨fun x hx => (partA_x M δ hδ 𝒬 h𝒬 x hx).1, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  by_cases hx : x ∈ M.X
  · rw [(partA_x M δ hδ 𝒬 h𝒬 x hx).2]
    simp [hx]
  · constructor
    · intro h; exact absurd h.1 hx
    · intro h; exact absurd h.1 hx

end SoftRobustT21Aux

open SoftRobust.Duality in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (M : Model Ω n m)
    (δ : ℝ) (hδ : 0 < δ) :
    (∀ 𝒬 : ℝ≥0 → Set (ProbabilityMeasure Ω), IsAdmissibleFamily 𝒬 →
      (IsConvexRiskMeasure (rhoQ 𝒬) ∧ IsGeneratedBy (rhoQ 𝒬) (penaltyOfFamily 𝒬) ∧
          IsNormalizedPenalty (penaltyOfFamily 𝒬)) ∧
        (∀ x ∈ M.X, ∃ l₀ ∈ Set.Ici (0 : ℝ),
          IsMinOn (dualObjective (rhoQ 𝒬) δ (M.payoff x)) (Set.Ici 0) l₀) ∧
        softRobustSet M 𝒬 δ =
          {x | x ∈ M.X ∧ ∃ l₀ ∈ Set.Ici (0 : ℝ),
            IsMinOn (dualObjective (rhoQ 𝒬) δ (M.payoff x)) (Set.Ici 0) l₀ ∧
              dualObjective (rhoQ 𝒬) δ (M.payoff x) l₀ ≤ 0}) ∧
    (∀ (α : ProbabilityMeasure Ω → ℝ≥0∞) (ρ : (Ω → ℝ) → ℝ),
      IsConvexRiskMeasure ρ → IsGeneratedBy ρ α → IsNormalizedPenalty α →
        IsAdmissibleFamily (familyOfPenalty α) ∧
        (∀ x ∈ M.X, ∃ l₀ ∈ Set.Ici (0 : ℝ),
          IsMinOn (dualObjective ρ δ (M.payoff x)) (Set.Ici 0) l₀) ∧
        softRobustSet M (familyOfPenalty α) δ =
          {x | x ∈ M.X ∧ ∃ l₀ ∈ Set.Ici (0 : ℝ),
            IsMinOn (dualObjective ρ δ (M.payoff x)) (Set.Ici 0) l₀ ∧
              dualObjective ρ δ (M.payoff x) l₀ ≤ 0}) := by
  refine ⟨fun 𝒬 h𝒬 => ⟨rhoQ_normalized_convex 𝒬 h𝒬, SoftRobustT21Aux.partA M δ hδ 𝒬 h𝒬⟩, ?_⟩
  intro α ρ _hρ hgen hnorm
  have hadm := familyOfPenalty_props α hgen.1 hnorm
  have hpen := penaltyOfFamily_familyOfPenalty α
  have hrho : ∀ Y : Ω → ℝ, IsBddPayoff Y → rhoQ (familyOfPenalty α) Y = ρ Y := by
    intro Y hY
    unfold rhoQ riskOfPenalty
    rw [hpen]
    obtain ⟨Q, hQ⟩ := hnorm
    exact (hgen.2 Y hY).csSup_eq ⟨_, Q, by simp [hQ], rfl⟩
  have hD : ∀ x ∈ M.X, dualObjective (rhoQ (familyOfPenalty α)) δ (M.payoff x) =
      dualObjective ρ δ (M.payoff x) := by
    intro x hx
    funext l
    unfold dualObjective
    rw [hrho _ (SoftRobustT21Aux.bdd_div (SoftRobustT21Aux.bdd_payoff M hx) _)]
  obtain ⟨hA1, hA2⟩ := SoftRobustT21Aux.partA M δ hδ (familyOfPenalty α) hadm
  refine ⟨hadm, fun x hx => ?_, ?_⟩
  · rw [← hD x hx]; exact hA1 x hx
  · rw [hA2]
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨hx, by rw [← hD x hx]; exact h⟩
    · rintro ⟨hx, h⟩; exact ⟨hx, by rw [hD x hx]; exact h⟩
