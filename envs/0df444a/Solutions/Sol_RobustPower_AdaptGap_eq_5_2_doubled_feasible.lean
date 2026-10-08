-- Prove2me | solution 1 for RobustPower.AdaptGap.eq_5_2_doubled_feasible
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:53:13.413973+00:00
-- url     : https://prove2.me/submissions/b09b35ab-febf-4476-ab30-4ca425a755fc

import Mathlib
import Definitions.Def_RobustPower_AdaptGap_Problems

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

private theorem mixed_double {n : ℕ} {I : Set (Fin n)} {x : Fin n → ℝ}
    (hx : x ∈ RobustPower.StochGap.mixedIntDomain I) :
    (2 : ℝ) • x ∈ RobustPower.StochGap.mixedIntDomain I := by
  constructor
  · intro i
    change 0 ≤ 2 * x i
    exact mul_nonneg (by norm_num) (hx.1 i)
  · intro i hi
    obtain ⟨z, hz⟩ := hx.2 i hi
    refine ⟨2 * z, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, hz, Int.cast_mul, Int.cast_ofNat]

/-- (5.2) and the p. 29 claim: doubling the center-scenario decisions is robust feasible. -/
theorem solution {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (ω₀ : Ω)
    (hb : ∀ ω, 0 ≤ b ω) (hd : ∀ ω, 0 ≤ d ω)
    (hfeas : AdaptFeasible A B b I₁ I₂ x y)
    (hcenter : RobustPower.StochGap.IsSymmetricAbout (scenarioSet b d) (b ω₀, d ω₀)) :
    RobustPower.StochGap.RobFeasible A B b I₁ I₂ ((2 : ℝ) • x) ((2 : ℝ) • y ω₀) := by
  refine ⟨mixed_double hfeas.1, mixed_double (hfeas.2 ω₀).1, ?_⟩
  intro ω
  have h := (scenario_bounds b d ω₀ hb hd hcenter ω).1
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_add]
  exact h.trans (smul_le_smul_of_nonneg_left (hfeas.2 ω₀).2 (by norm_num))
