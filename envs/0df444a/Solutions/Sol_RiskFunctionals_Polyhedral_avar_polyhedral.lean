-- Prove2me | solution 1 for RiskFunctionals.Polyhedral.avar_polyhedral
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:11:45.884987+00:00
-- url     : https://prove2.me/submissions/a1343499-3d06-428b-b69a-6b12dce31b44

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones
import Definitions.Def_RiskFunctionals_Polyhedral_SinglePeriod

open MeasureTheory ProbabilityTheory RiskFunctionals.Polyhedral

/-- strict increase of x ↦ x - E (x - Y)^+ when Y is not bounded above -/
theorem g79p_strict (G : Measure ℝ) [IsProbabilityMeasure G] (hY : Integrable (fun y : ℝ => y) G)
    (hpos : ∀ x : ℝ, G (Set.Ioi x) ≠ 0) (x : ℝ) :
    x - ∫ y, max (x - y) 0 ∂G < (x + 1) - ∫ y, max (x + 1 - y) 0 ∂G := by
  have hi : ∀ c : ℝ, Integrable (fun y : ℝ => max (c - y) 0) G :=
    fun c => ((integrable_const c).sub hY).pos_part
  set d : ℝ → ℝ := fun y => 1 - (max (x + 1 - y) 0 - max (x - y) 0) with hd
  have hdi : Integrable d G := (integrable_const 1).sub ((hi (x + 1)).sub (hi x))
  have hdnn : 0 ≤ᵐ[G] d := Filter.Eventually.of_forall fun y => by
    simp only [hd, Pi.zero_apply]
    rcases le_total (x + 1 - y) 0 with h1 | h1 <;> rcases le_total (x - y) 0 with h2 | h2
    · rw [max_eq_right h1, max_eq_right h2]; norm_num
    · linarith
    · rw [max_eq_left h1, max_eq_right h2]; linarith
    · rw [max_eq_left h1, max_eq_left h2]; linarith
  have hdpos : 0 < ∫ y, d y ∂G := by
    rw [integral_pos_iff_support_of_nonneg_ae hdnn hdi]
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr (hpos x)) (measure_mono fun y hy => ?_)
    have hy' : x < y := hy
    simp only [Function.mem_support, hd]
    rw [max_eq_right (by linarith : x - y ≤ 0)]
    intro h0
    have : max (x + 1 - y) 0 = 1 := by linarith
    rcases le_total (x + 1 - y) 0 with h1 | h1
    · rw [max_eq_right h1] at this; norm_num at this
    · rw [max_eq_left h1] at this; linarith
  have e1 : ∫ y, d y ∂G = ∫ y, (1:ℝ) ∂G - ∫ y, (max (x + 1 - y) 0 - max (x - y) 0) ∂G :=
    integral_sub (integrable_const 1) ((hi (x + 1)).sub (hi x))
  have e2 : ∫ y, (max (x + 1 - y) 0 - max (x - y) 0) ∂G =
      ∫ y, max (x + 1 - y) 0 ∂G - ∫ y, max (x - y) 0 ∂G := integral_sub (hi (x + 1)) (hi x)
  have e3 : ∫ y, (1:ℝ) ∂G = 1 := by simp
  rw [e1, e2, e3] at hdpos
  linarith

theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ = 1) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1),

    (avarData α).IsPolyhedral ∧ IsPolyhedralCone (avarData α).V₀ ∧
    IsPolyhedralCone (avarData α).V₁ ∧
    (∀ Y : Ω → ℝ, MemLp Y p P →
      (avarData α).functional P p Y ≠ ⊥ ∧ (avarData α).functional P p Y ≠ ⊤ ∧
      IsGreatest {y : ℝ | ∃ x : ℝ, y = x - (1 / α) * ∫ ω, max (x - Y ω) 0 ∂P}
        ((avarData α).functional P p Y).toReal) ∧
    IsAcceptabilityFunctional P p (fun Y => ((avarData α).functional P p Y).toReal) ∧
    (avarData α).CompleteRecourse ∧
    (avarData α).dualFeasibleSet = {1} ∧
    (avarData α).dualSet P q =
      {Z : Ω → ℝ | MemLp Z q P ∧ ∫ ω, Z ω ∂P = 1 ∧
        ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ 1 / α}) := by
  intro h
  set G := gaussianReal 0 1 with hG
  have hmem : MemLp (fun x : ℝ => x) 1 G := memLp_id_gaussianReal' 1 (by simp)
  have hpq : (1 : ENNReal)⁻¹ + (⊤ : ENNReal)⁻¹ = 1 := by simp
  obtain ⟨-, -, -, hY, -⟩ := h G 1 ⊤ le_rfl ENNReal.one_ne_top hpq 1 one_pos le_rfl
  obtain ⟨⟨x, hx⟩, hub⟩ := (hY (fun x => x) hmem).2.2
  have hac := gaussianReal_absolutelyContinuous' 0 (v := 1) one_ne_zero
  have hpos : ∀ x : ℝ, G (Set.Ioi x) ≠ 0 := by
    intro x hx0
    have := hac hx0
    simp at this
  have hs := g79p_strict G (hmem.integrable le_rfl) hpos x
  have := hub ⟨x + 1, rfl⟩
  simp only [div_one, one_mul] at hx this hs
  linarith
