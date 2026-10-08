-- Prove2me | solution 1 for RobustPower.StochGap.theorem_2_7_positive_robust_le_two_stoch
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:14:48.356031+00:00
-- url     : https://prove2.me/submissions/38daa351-9c77-41df-9714-0e953e5c8760

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_StochGap_Problems

set_option autoImplicit false

open MeasureTheory Matrix in
lemma p66c3_mean_policy {m n₁ n₂ : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (hbint : Integrable b μ)
    (x : Fin n₁ → ℝ) (y : Ω → Fin n₂ → ℝ) (hyint : Integrable y μ) (hy : ∀ ω, 0 ≤ y ω)
    (hfeas : ∀ ω, b ω ≤ A *ᵥ x + B *ᵥ y ω) :
    0 ≤ ∫ ω, y ω ∂μ ∧ ∫ ω, b ω ∂μ ≤ A *ᵥ x + B *ᵥ (∫ ω, y ω ∂μ) := by
  have hyi : ∀ j, Integrable (fun ω => y ω j) μ := hyint.eval
  have hbi : ∀ i, Integrable (fun ω => b ω i) μ := hbint.eval
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [Pi.zero_apply, eval_integral hyi]
    exact integral_nonneg (fun ω => hy ω j)
  · rw [eval_integral hbi]
    have key : (B *ᵥ ∫ ω, y ω ∂μ) i = ∫ ω, (B *ᵥ y ω) i ∂μ := by
      simp only [Matrix.mulVec, dotProduct]
      rw [integral_finsetSum _ (fun j _ => (hyi j).const_mul (B i j))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [eval_integral hyi, integral_const_mul]
    have hint : Integrable (fun ω => (B *ᵥ y ω) i) μ := by
      simp only [Matrix.mulVec, dotProduct]
      exact integrable_finsetSum _ (fun j _ => (hyi j).const_mul (B i j))
    calc ∫ ω, b ω i ∂μ
        ≤ ∫ ω, ((A *ᵥ x) i + (B *ᵥ y ω) i) ∂μ :=
          integral_mono (hbi i) ((integrable_const _).add hint) (fun ω => hfeas ω i)
      _ = (A *ᵥ x + B *ᵥ (∫ ω, y ω ∂μ)) i := by
          rw [integral_add (integrable_const _) hint, integral_const, ← key]
          simp

open MeasureTheory Matrix in
lemma p66c3_dot_integral {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : Fin n → ℝ) (y : Ω → Fin n → ℝ) (hyint : Integrable y μ) :
    d ⬝ᵥ (∫ ω, y ω ∂μ) = ∫ ω, d ⬝ᵥ y ω ∂μ := by
  have hyi : ∀ j, Integrable (fun ω => y ω j) μ := hyint.eval
  simp only [dotProduct]
  rw [integral_finsetSum _ (fun j _ => (hyi j).const_mul (d j))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [eval_integral hyi, integral_const_mul]

open MeasureTheory Matrix RobustPower.StochGap in
theorem solution {m n₁ n₂ : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (b : Ω → Fin m → ℝ) (hb : ∀ ω, 0 ≤ b ω) (hbint : Integrable b μ)
    (I₁ : Set (Fin n₁))
    (hpos : IsPositive (Set.range b))
    (T : Set (Fin m → ℝ)) (b₀ : Fin m → ℝ) (hT : ∀ t ∈ T, 0 ≤ t)
    (hTsym : IsSymmetricAbout T b₀) (hsub : Set.range b ⊆ T) (hb₀ : b₀ ∈ Set.range b)
    (hmean : b₀ ≤ ∫ ω, b ω ∂μ) :
    zRob A B b I₁ ∅ c d ≤ 2 * zStoch μ A B b I₁ ∅ c d := by
  have h2 : (0 : EReal) < 2 := by norm_num
  have h2' : (2 : EReal) ≠ ⊤ := by
    have : ((2 : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top 2
    exact_mod_cast this
  -- every scenario is at most `2 b₀`
  have hb2 : ∀ ω i, b ω i ≤ 2 * b₀ i := by
    intro ω i
    have hbT : b ω ∈ T := hsub ⟨ω, rfl⟩
    have h1 : b₀ + (b ω - b₀) ∈ T := by rwa [add_sub_cancel]
    have h3 : b₀ - (b ω - b₀) ∈ T := (hTsym.2 (b ω - b₀)).1 h1
    have h4 := hT _ h3 i
    simp only [Pi.zero_apply, Pi.sub_apply] at h4
    linarith
  rw [← EReal.div_le_iff_le_mul h2 h2']
  unfold zStoch
  refine le_iInf fun x => le_iInf fun y => le_iInf fun hf => ?_
  rw [EReal.div_le_iff_le_mul h2 h2']
  obtain ⟨hx, hyint, hy⟩ := hf
  obtain ⟨hy0, hmv⟩ := p66c3_mean_policy μ A B b hbint x y hyint (fun ω => (hy ω).1.1)
    (fun ω => (hy ω).2)
  set ybar := ∫ ω, y ω ∂μ with hybar
  have hrob : RobFeasible A B b I₁ ∅ ((2 : ℝ) • x) ((2 : ℝ) • ybar) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · intro i
      have := hx.1 i
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      linarith
    · intro i hi
      obtain ⟨z, hz⟩ := hx.2 i hi
      exact ⟨2 * z, by simp [hz]⟩
    · intro i
      have := hy0 i
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      linarith
    · intro i hi
      exact absurd hi (Set.notMem_empty i)
    · intro ω i
      have e1 := hb2 ω i
      have e2 := hmean i
      have e3 := hmv i
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e3 ⊢
      linarith
  have hval : c ⬝ᵥ ((2 : ℝ) • x) + d ⬝ᵥ ((2 : ℝ) • ybar)
      = 2 * (c ⬝ᵥ x + ∫ ω, d ⬝ᵥ y ω ∂μ) := by
    rw [dotProduct_smul, dotProduct_smul, hybar, p66c3_dot_integral μ d y hyint]
    simp only [smul_eq_mul]
    ring
  calc zRob A B b I₁ ∅ c d
      ≤ ((c ⬝ᵥ ((2 : ℝ) • x) + d ⬝ᵥ ((2 : ℝ) • ybar) : ℝ) : EReal) :=
        iInf_le_of_le ((2 : ℝ) • x) (iInf_le_of_le ((2 : ℝ) • ybar) (iInf_le_of_le hrob le_rfl))
    _ = 2 * ((c ⬝ᵥ x + ∫ ω, d ⬝ᵥ y ω ∂μ : ℝ) : EReal) := by
        rw [hval, EReal.coe_mul]
        rfl
