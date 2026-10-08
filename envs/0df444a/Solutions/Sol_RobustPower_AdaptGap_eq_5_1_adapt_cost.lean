-- Prove2me | solution 1 for RobustPower.AdaptGap.eq_5_1_adapt_cost
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:53:10.569235+00:00
-- url     : https://prove2.me/submissions/7c2eff20-5dbe-45a5-b31d-de03971364f5

import Mathlib
import Definitions.Def_RobustPower_AdaptGap_Problems

open Matrix

open Matrix RobustPower.AdaptGap

private theorem reflect_mem {E : Type*} [AddCommGroup E] {S : Set E} {u x : E}
    (hsym : RobustPower.StochGap.IsSymmetricAbout S u) (hx : x ∈ S) :
    u - (x - u) ∈ S := by
  apply (hsym.2 (x - u)).mp
  simpa only [add_sub_cancel] using hx

private theorem scenario_bounds {m n₂ : ℕ} {Ω : Type*}
    (b : Ω → Fin m → ℝ) (d : Ω → Fin n₂ → ℝ) (ω₀ : Ω)
    (hb : ∀ ω, 0 ≤ b ω) (hd : ∀ ω, 0 ≤ d ω)
    (hsym : RobustPower.StochGap.IsSymmetricAbout (scenarioSet b d) (b ω₀, d ω₀)) :
    ∀ ω, b ω ≤ (2 : ℝ) • b ω₀ ∧ d ω ≤ (2 : ℝ) • d ω₀ := by
  intro ω
  have hr := reflect_mem hsym (show (b ω, d ω) ∈ scenarioSet b d from ⟨ω, rfl⟩)
  obtain ⟨ω', hω'⟩ := hr
  have heqb := congrArg Prod.fst hω'
  have heqd := congrArg Prod.snd hω'
  constructor
  · intro j
    have hn := hb ω' j
    have heq := congrFun heqb j
    change b ω' j = b ω₀ j - (b ω j - b ω₀ j) at heq
    change b ω j ≤ 2 * b ω₀ j
    change 0 ≤ b ω' j at hn
    linarith
  · intro j
    have hn := hd ω' j
    have heq := congrFun heqd j
    change d ω' j = d ω₀ j - (d ω j - d ω₀ j) at heq
    change d ω j ≤ 2 * d ω₀ j
    change 0 ≤ d ω' j at hn
    linarith

/-- Inequality (5.1), p. 28, for an arbitrary feasible adaptive solution. -/
theorem solution {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (ω₀ : Ω)
    (hc : 0 ≤ c) (hb : ∀ ω, 0 ≤ b ω) (hd : ∀ ω, 0 ≤ d ω)
    (hfeas : AdaptFeasible A B b I₁ I₂ x y)
    (hcenter : RobustPower.StochGap.IsSymmetricAbout (scenarioSet b d) (b ω₀, d ω₀)) :
    (((c ⬝ᵥ x + (costUpper d / 2) ⬝ᵥ y ω₀ : ℝ) : EReal) ≤
      adaptCost c d x y) := by
  have hu : costUpper d ≤ (2 : ℝ) • d ω₀ := by
    intro j
    apply csSup_le
    · exact ⟨d ω₀ j, d ω₀, ⟨ω₀, rfl⟩, rfl⟩
    · rintro _ ⟨v, ⟨ω, rfl⟩, rfl⟩
      exact (scenario_bounds b d ω₀ hb hd hcenter ω).2 j
  have hhalf : costUpper d / 2 ≤ d ω₀ := by
    intro j
    have h := hu j
    change costUpper d j / 2 ≤ d ω₀ j
    change costUpper d j ≤ 2 * d ω₀ j at h
    linarith
  have hdot : (costUpper d / 2) ⬝ᵥ y ω₀ ≤ d ω₀ ⬝ᵥ y ω₀ := by
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hhalf i) ((hfeas.2 ω₀).1.1 i))
  calc
    _ ≤ ((c ⬝ᵥ x + d ω₀ ⬝ᵥ y ω₀ : ℝ) : EReal) := by
      exact EReal.coe_le_coe_iff.mpr (add_le_add le_rfl hdot)
    _ ≤ adaptCost c d x y := by
      rw [EReal.coe_add]
      exact add_le_add le_rfl (le_iSup (fun ω => ((d ω ⬝ᵥ y ω : ℝ) : EReal)) ω₀)
