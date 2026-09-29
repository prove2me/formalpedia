-- Prove2me | solution 1 for VapnikChervonenkis.Entropy.entropy_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:05:21.728323+00:00
-- url     : https://prove2.me/submissions/1edc4228-db91-480f-8b54-f38c50ae96fe

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Entropy_entropy

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- The index of a concatenated sample is at most the product of the indices. -/
theorem aux_esub_index_append_le {X : Type*} (S : Set (Set X)) {l₁ l₂ : ℕ}
    (x : Fin l₁ → X) (y : Fin l₂ → X) :
    Shared.index S (Fin.append x y) ≤ Shared.index S x * Shared.index S y := by
  classical
  unfold Shared.index
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn
    (fun t => (Finset.univ.filter (fun i => Fin.castAdd l₂ i ∈ t),
      Finset.univ.filter (fun i => Fin.natAdd l₁ i ∈ t))) ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht
    obtain ⟨A, hA, hAt⟩ := ht
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_prod, Set.mem_setOf_eq]
    refine ⟨⟨A, hA, fun i => ?_⟩, ⟨A, hA, fun i => ?_⟩⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hAt, Fin.append_left]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hAt, Fin.append_right]
  · intro t _ t' _ h
    simp only [Prod.mk.injEq, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    obtain ⟨h1, h2⟩ := h
    ext i
    induction i using Fin.addCases with
    | left j => exact h1 j
    | right j => exact h2 j

theorem aux_esub_index_le {X : Type*} (S : Set (Set X)) {n : ℕ} (x : Fin n → X) :
    Shared.index S x ≤ 2 ^ n := by
  classical
  unfold Shared.index
  calc _ ≤ (Finset.univ : Finset (Finset (Fin n))).card := Finset.card_filter_le _ _
    _ = 2 ^ n := by simp

theorem aux_esub_logb_nonneg (k : ℕ) : 0 ≤ Real.logb 2 (k : ℝ) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · simp [h]
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

theorem aux_esub_logb_le {X : Type*} (S : Set (Set X)) {n : ℕ} (x : Fin n → X) :
    Real.logb 2 (Shared.index S x : ℝ) ≤ n := by
  rcases Nat.eq_zero_or_pos (Shared.index S x) with h | h
  · simp [h]
  · have h1 : ((Shared.index S x : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast aux_esub_index_le S x
    calc Real.logb 2 (Shared.index S x : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ n) :=
          Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h) h1
      _ = n := by rw [Real.logb_pow]; simp

theorem aux_esub_logb_append_le {X : Type*} (S : Set (Set X)) {l₁ l₂ : ℕ}
    (x : Fin l₁ → X) (y : Fin l₂ → X) :
    Real.logb 2 (Shared.index S (Fin.append x y) : ℝ) ≤
      Real.logb 2 (Shared.index S x : ℝ) + Real.logb 2 (Shared.index S y : ℝ) := by
  have hle := aux_esub_index_append_le S x y
  rcases Nat.eq_zero_or_pos (Shared.index S (Fin.append x y)) with h | h
  · rw [h]
    simp only [Nat.cast_zero, Real.logb_zero]
    exact add_nonneg (aux_esub_logb_nonneg _) (aux_esub_logb_nonneg _)
  · have hpos : 0 < Shared.index S x * Shared.index S y := lt_of_lt_of_le h hle
    have hx : Shared.index S x ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hpos; exact lt_irrefl _ hpos
    have hy : Shared.index S y ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
    rw [← Real.logb_mul (by exact_mod_cast hx) (by exact_mod_cast hy)]
    apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h)
    exact_mod_cast hle

theorem aux_esub_measurable_append {X : Type*} [MeasurableSpace X] (l₁ l₂ : ℕ) :
    Measurable (fun p : (Fin l₁ → X) × (Fin l₂ → X) => Fin.append p.1 p.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  induction i using Fin.addCases with
  | left j =>
    simp only [Fin.append_left]
    exact (measurable_pi_apply j).comp measurable_fst
  | right j =>
    simp only [Fin.append_right]
    exact (measurable_pi_apply j).comp measurable_snd

theorem aux_esub_mp {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (l₁ l₂ : ℕ) :
    MeasurePreserving (fun p : (Fin l₁ → X) × (Fin l₂ → X) => Fin.append p.1 p.2)
      ((Measure.pi fun _ : Fin l₁ => P).prod (Measure.pi fun _ : Fin l₂ => P))
      (Measure.pi fun _ : Fin (l₁ + l₂) => P) := by
  refine ⟨aux_esub_measurable_append l₁ l₂, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply (aux_esub_measurable_append l₁ l₂) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin l₁ → X) × (Fin l₂ → X) => Fin.append p.1 p.2) ⁻¹'
      (Set.univ.pi s) =
      (Set.univ.pi fun i => s (Fin.castAdd l₂ i)) ×ˢ
        (Set.univ.pi fun j => s (Fin.natAdd l₁ j)) := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    rw [Fin.forall_fin_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fin.prod_univ_add]

end VapnikChervonenkis.Entropy

open VapnikChervonenkis VapnikChervonenkis.Entropy
open MeasureTheory Filter Topology

theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x))
    (l₁ l₂ : ℕ) :
    entropy S P (l₁ + l₂) ≤ entropy S P l₁ + entropy S P l₂ := by
  set μ₁ := Measure.pi fun _ : Fin l₁ => P
  set μ₂ := Measure.pi fun _ : Fin l₂ => P
  have hg : ∀ n : ℕ, Measurable
      (fun x : Fin n → X => Real.logb 2 (Shared.index S x : ℝ)) :=
    fun n => (measurable_from_nat (f := fun k : ℕ => Real.logb 2 (k : ℝ))).comp (hΔ n)
  have hnorm : ∀ n : ℕ, ∀ x : Fin n → X,
      ‖Real.logb 2 (Shared.index S x : ℝ)‖ ≤ n := by
    intro n x
    rw [Real.norm_of_nonneg (aux_esub_logb_nonneg _)]
    exact aux_esub_logb_le S x
  have hmp := aux_esub_mp P l₁ l₂
  unfold entropy
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (hg (l₁ + l₂)).aestronglyMeasurable]
  have hint1 : Integrable (fun p : (Fin l₁ → X) × (Fin l₂ → X) =>
      Real.logb 2 (Shared.index S p.1 : ℝ)) (μ₁.prod μ₂) :=
    Integrable.of_bound ((hg l₁).comp measurable_fst).aestronglyMeasurable l₁
      (ae_of_all _ fun p => hnorm l₁ p.1)
  have hint2 : Integrable (fun p : (Fin l₁ → X) × (Fin l₂ → X) =>
      Real.logb 2 (Shared.index S p.2 : ℝ)) (μ₁.prod μ₂) :=
    Integrable.of_bound ((hg l₂).comp measurable_snd).aestronglyMeasurable l₂
      (ae_of_all _ fun p => hnorm l₂ p.2)
  have hint0 : Integrable (fun p : (Fin l₁ → X) × (Fin l₂ → X) =>
      Real.logb 2 (Shared.index S (Fin.append p.1 p.2) : ℝ))
      (μ₁.prod μ₂) :=
    Integrable.of_bound ((hg (l₁ + l₂)).comp hmp.measurable).aestronglyMeasurable (l₁ + l₂ : ℕ)
      (ae_of_all _ fun p => hnorm (l₁ + l₂) _)
  calc ∫ p, Real.logb 2 (Shared.index S (Fin.append p.1 p.2) : ℝ)
          ∂(μ₁.prod μ₂)
        ≤ ∫ p, (Real.logb 2 (Shared.index S p.1 : ℝ) +
            Real.logb 2 (Shared.index S p.2 : ℝ)) ∂(μ₁.prod μ₂) :=
          integral_mono hint0 (hint1.add hint2)
            (fun p => aux_esub_logb_append_le S p.1 p.2)
      _ = ∫ p, Real.logb 2 (Shared.index S p.1 : ℝ) ∂(μ₁.prod μ₂) +
            ∫ p, Real.logb 2 (Shared.index S p.2 : ℝ) ∂(μ₁.prod μ₂) :=
          integral_add hint1 hint2
      _ = _ := by
          rw [integral_fun_fst (fun x : Fin l₁ → X =>
                Real.logb 2 (Shared.index S x : ℝ)),
              integral_fun_snd (fun x : Fin l₂ → X =>
                Real.logb 2 (Shared.index S x : ℝ))]
          simp [μ₁, μ₂]
