-- Prove2me | solution 1 for bernoulli_centered_sampling_fluctuation_entry_sum_chernoff_mgf_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-29T00:36:08.495798+00:00
-- url     : https://prove2.me/submissions/a31a6e96-3d36-4a2c-9a7f-9bf6ef775a4f

import Mathlib
import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators
open Finset

-- prod_add core: sum over all subsets of a product-of-ite equals product of sums
lemma sum_prod_ite {σ : Type*} [Fintype σ] [DecidableEq σ] (a b : σ → ℝ) :
    (∑ Ω : Finset σ, ∏ w, (if w ∈ Ω then a w else b w)) = ∏ w, (a w + b w) := by
  rw [Finset.prod_add]
  rw [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro Ω _
  rw [Finset.prod_ite]
  congr 1
  · -- ∏ over univ.filter (·∈Ω) of a = ∏ over Ω of a
    apply Finset.prod_congr ?_ (fun _ _ => rfl)
    ext w; simp [Finset.mem_filter]
  · -- ∏ over univ.filter (·∉Ω) of b = ∏ over univ\Ω of b
    apply Finset.prod_congr ?_ (fun _ _ => rfl)
    ext w; simp [Finset.mem_filter, Finset.mem_sdiff]

-- MGF factorization for the centered statistic Z(Ω) = ∑_w X_w (1[w∈Ω] - p)
lemma mgf_fluct {n₁ n₂ : ℕ} (p s : ℝ) (X : Fin n₁ × Fin n₂ → ℝ) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂),
        (p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card))
          * Real.exp (s * ∑ w : Fin n₁ × Fin n₂, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p)))
      = ∏ w : Fin n₁ × Fin n₂,
          Real.exp (-(s * p * X w)) * (1 - p + p * Real.exp (s * X w)) := by
  -- rewrite each summand as ∏_w (if w∈Ω then p e^{sX} else 1-p) times the constant ∏ e^{-spX}
  have hconst : ∀ Ω : Finset (Fin n₁ × Fin n₂),
      (p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card))
          * Real.exp (s * ∑ w, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))
        = (∏ w : Fin n₁ × Fin n₂, Real.exp (-(s * p * X w)))
            * ∏ w : Fin n₁ × Fin n₂,
                (if w ∈ Ω then p * Real.exp (s * X w) else (1 - p)) := by
    intro Ω
    -- weight as product of ite
    have hc1 : (univ.filter (fun w : Fin n₁ × Fin n₂ => w ∈ Ω)).card = Ω.card := by
      rw [show univ.filter (fun w : Fin n₁ × Fin n₂ => w ∈ Ω) = Ω from by ext w; simp]
    have hc2 : (univ.filter (fun w : Fin n₁ × Fin n₂ => w ∉ Ω)).card
        = Fintype.card (Fin n₁ × Fin n₂) - Ω.card := by
      rw [show univ.filter (fun w : Fin n₁ × Fin n₂ => w ∉ Ω) = Ωᶜ from by ext w; simp,
        Finset.card_compl]
    have hweight : p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card)
        = ∏ w : Fin n₁ × Fin n₂, (if w ∈ Ω then p else (1 - p)) := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hc1, hc2]
    -- exp of sum = product
    have hexp : Real.exp (s * ∑ w, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))
        = ∏ w : Fin n₁ × Fin n₂,
            (Real.exp (-(s * p * X w)) * (if w ∈ Ω then Real.exp (s * X w) else 1)) := by
      rw [Finset.mul_sum, Real.exp_sum]
      apply Finset.prod_congr rfl
      intro w _
      by_cases h : w ∈ Ω
      · simp only [if_pos h]
        rw [show s * (X w * ((1:ℝ) - p)) = -(s * p * X w) + s * X w from by ring, Real.exp_add]
      · simp only [if_neg h]
        rw [show s * (X w * ((0:ℝ) - p)) = -(s * p * X w) from by ring, mul_one]
    rw [hweight, hexp, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro w _
    by_cases h : w ∈ Ω <;> simp [h] <;> ring
  rw [Finset.sum_congr rfl (fun Ω _ => hconst Ω), ← Finset.mul_sum, sum_prod_ite]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro w _
  ring

-- Bennett MGF bound: MGF ≤ exp(∑ p (e^{sX}-1-sX))
lemma mgf_fluct_le {n₁ n₂ : ℕ} (p s : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : Fin n₁ × Fin n₂ → ℝ) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂),
        (p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card))
          * Real.exp (s * ∑ w : Fin n₁ × Fin n₂, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p)))
      ≤ Real.exp (∑ w : Fin n₁ × Fin n₂, p * (Real.exp (s * X w) - 1 - s * X w)) := by
  rw [mgf_fluct, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro w _
    have h := Real.exp_pos (s * X w)
    apply mul_nonneg (Real.exp_pos _).le
    nlinarith [h, hp0, hp1]
  · intro w _
    have hE := Real.exp_pos (s * X w)
    have h1 : (1 - p + p * Real.exp (s * X w)) ≤ Real.exp (p * (Real.exp (s * X w) - 1)) := by
      have := Real.add_one_le_exp (p * (Real.exp (s * X w) - 1))
      nlinarith [this]
    calc Real.exp (-(s * p * X w)) * (1 - p + p * Real.exp (s * X w))
        ≤ Real.exp (-(s * p * X w)) * Real.exp (p * (Real.exp (s * X w) - 1)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (p * (Real.exp (s * X w) - 1 - s * X w)) := by
          rw [← Real.exp_add]; congr 1; ring

-- One-sided Chernoff tail for Z(Ω) = ∑_w X_w (1[w∈Ω] - p)
lemma fluct_chernoff {n₁ n₂ : ℕ} (p s t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 ≤ s)
    (X : Fin n₁ × Fin n₂ → ℝ) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂),
        if t < (∑ w : Fin n₁ × Fin n₂, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))
        then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
      ≤ Real.exp (-(s * t) + ∑ w : Fin n₁ × Fin n₂, p * (Real.exp (s * X w) - 1 - s * X w)) := by
  have hmarkov : (∑ Ω : Finset (Fin n₁ × Fin n₂),
        if t < (∑ w, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))
        then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
      ≤ ∑ Ω : Finset (Fin n₁ × Fin n₂),
          Real.exp (-(s * t)) *
            ((p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card))
              * Real.exp (s * ∑ w, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))) := by
    apply Finset.sum_le_sum
    intro Ω _
    set Z := (∑ w, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p)) with hZ
    set W := p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) with hW
    have hWnn : 0 ≤ W := mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
    by_cases h : t < Z
    · rw [if_pos h]
      have h1 : (1 : ℝ) ≤ Real.exp (-(s * t)) * Real.exp (s * Z) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]; nlinarith [hs, h]
      calc W = 1 * W := (one_mul _).symm
        _ ≤ (Real.exp (-(s * t)) * Real.exp (s * Z)) * W := mul_le_mul_of_nonneg_right h1 hWnn
        _ = Real.exp (-(s * t)) * (W * Real.exp (s * Z)) := by ring
    · rw [if_neg h]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hWnn (Real.exp_pos _).le)
  refine le_trans hmarkov ?_
  rw [← Finset.mul_sum, Real.exp_add]
  exact mul_le_mul_of_nonneg_left (mgf_fluct_le p s hp0 hp1 X) (Real.exp_pos _).le

-- ecosystem-native one-sided Chernoff/MGF tail for the centered sampling fluctuation entry sum
theorem solution {n₁ n₂ : ℕ} (p s t : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 ≤ s) :
    bernoulliEventProb p (fun Ω => t < matrixEntrySum (centeredSamplingFluctuation Ω p X))
      ≤ Real.exp (-(s * t) + ∑ w : Fin n₁ × Fin n₂,
          p * (Real.exp (s * (p⁻¹ * X w.1 w.2)) - 1 - s * (p⁻¹ * X w.1 w.2))) := by
  have hY : ∀ Ω : Finset (Fin n₁ × Fin n₂),
      matrixEntrySum (centeredSamplingFluctuation Ω p X)
        = ∑ w : Fin n₁ × Fin n₂, (p⁻¹ * X w.1 w.2) * ((if w ∈ Ω then (1 : ℝ) else 0) - p) := by
    intro Ω
    unfold matrixEntrySum centeredSamplingFluctuation
    apply Finset.sum_congr rfl
    intro w _
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    unfold samplingProjection
    by_cases h : w ∈ Ω <;> simp [h] <;> ring
  unfold bernoulliEventProb bernoulliObservationWeight
  rw [show (fun Ω => t < matrixEntrySum (centeredSamplingFluctuation Ω p X))
        = (fun Ω => t < ∑ w : Fin n₁ × Fin n₂,
            (p⁻¹ * X w.1 w.2) * ((if w ∈ Ω then (1 : ℝ) else 0) - p))
      from by funext Ω; rw [hY]]
  exact fluct_chernoff p s t hp0 hp1 hs (fun w => p⁻¹ * X w.1 w.2)
