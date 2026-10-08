-- Prove2me | solution 1 for RobustPower.AdaptGap.theorem_5_1_robust_le_four_adapt
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:53:19.176219+00:00
-- url     : https://prove2.me/submissions/d6e8b6ee-ff42-4a0a-8296-b95be77fce71

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

private theorem feasibility {m n₁ n₂ : ℕ} {Ω : Type*}
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

private theorem cost_bound {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (ω₀ : Ω)
    (hc : 0 ≤ c) (hb : ∀ ω, 0 ≤ b ω) (hd : ∀ ω, 0 ≤ d ω)
    (hfeas : AdaptFeasible A B b I₁ I₂ x y)
    (hcenter : RobustPower.StochGap.IsSymmetricAbout (scenarioSet b d) (b ω₀, d ω₀)) :
    robCost c d ((2 : ℝ) • x) ((2 : ℝ) • y ω₀) ≤
      (4 : EReal) * adaptCost c d x y := by
  have hcx : 0 ≤ c ⬝ᵥ x :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hc i) (hfeas.1.1 i))
  have hpoint : ∀ ω, d ω ⬝ᵥ ((2 : ℝ) • y ω₀) ≤ 4 * (d ω₀ ⬝ᵥ y ω₀) := by
    intro ω
    have hdot : d ω ⬝ᵥ y ω₀ ≤ ((2 : ℝ) • d ω₀) ⬝ᵥ y ω₀ :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
        ((scenario_bounds b d ω₀ hb hd hcenter ω).2 i) ((hfeas.2 ω₀).1.1 i))
    rw [smul_dotProduct, smul_eq_mul] at hdot
    rw [dotProduct_smul, smul_eq_mul]
    linarith
  have hrob : robCost c d ((2 : ℝ) • x) ((2 : ℝ) • y ω₀) ≤
      ((2 * (c ⬝ᵥ x) + 4 * (d ω₀ ⬝ᵥ y ω₀) : ℝ) : EReal) := by
    unfold robCost
    rw [dotProduct_smul, smul_eq_mul, EReal.coe_add]
    exact add_le_add le_rfl (iSup_le fun ω => EReal.coe_le_coe_iff.mpr (hpoint ω))
  have hadapt : ((c ⬝ᵥ x + d ω₀ ⬝ᵥ y ω₀ : ℝ) : EReal) ≤ adaptCost c d x y := by
    rw [EReal.coe_add]
    exact add_le_add le_rfl (le_iSup (fun ω => ((d ω ⬝ᵥ y ω : ℝ) : EReal)) ω₀)
  calc
    _ ≤ ((2 * (c ⬝ᵥ x) + 4 * (d ω₀ ⬝ᵥ y ω₀) : ℝ) : EReal) := hrob
    _ ≤ ((4 * (c ⬝ᵥ x + d ω₀ ⬝ᵥ y ω₀) : ℝ) : EReal) := by
      apply EReal.coe_le_coe_iff.mpr
      linarith
    _ = (4 : EReal) * ((c ⬝ᵥ x + d ω₀ ⬝ᵥ y ω₀ : ℝ) : EReal) := by
      rw [EReal.coe_mul]
      rfl
    _ ≤ (4 : EReal) * adaptCost c d x y :=
      mul_le_mul_of_nonneg_left hadapt (by norm_num)

/-- Theorem 5.1, p. 28: the adaptability gap is at most four. -/
theorem solution {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (hc : 0 ≤ c) (hb : ∀ ω, 0 ≤ b ω) (hd : ∀ ω, 0 ≤ d ω)
    (hsym : RobustPower.StochGap.IsSymmetric (scenarioSet b d)) :
    zRob A B b c d I₁ I₂ ≤ (4 : EReal) * zAdapt A B b c d I₁ I₂ := by
  obtain ⟨u, hu⟩ := hsym
  obtain ⟨ω₀, rfl⟩ := hu.1
  apply (EReal.div_le_iff_le_mul (by norm_num : (0 : EReal) < 4) (EReal.natCast_ne_top 4)).mp
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply le_iInf
  intro hfeas
  apply (EReal.div_le_iff_le_mul (by norm_num : (0 : EReal) < 4) (EReal.natCast_ne_top 4)).mpr
  have hf := feasibility A B b d I₁ I₂ x y ω₀ hb hd hfeas hu
  have hz : zRob A B b c d I₁ I₂ ≤ robCost c d ((2 : ℝ) • x) ((2 : ℝ) • y ω₀) :=
    iInf_le_of_le _ (iInf_le_of_le _ (iInf_le _ hf))
  exact hz.trans (cost_bound A B b c d I₁ I₂ x y ω₀ hc hb hd hfeas hu)
