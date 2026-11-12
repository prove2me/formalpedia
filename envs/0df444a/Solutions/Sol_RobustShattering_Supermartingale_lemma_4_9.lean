-- Prove2me | solution 1 for RobustShattering.Supermartingale.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:35:58.542392+00:00
-- url     : https://prove2.me/submissions/3e7bfd86-3421-4c92-9c52-d6f3c253876d

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_RobustShattering_Supermartingale_Shatterable
import Theorems.Thm_RobustShattering_Supermartingale_lemma_4_8

section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace RobustShattering.Dev.L49

theorem lintegral_update {ι : Type} [Fintype ι] [DecidableEq ι] {β : ι → Type}
    [∀ k, MeasurableSpace (β k)] (π : ∀ k, Measure (β k)) [∀ k, IsProbabilityMeasure (π k)]
    (k : ι) (F : (∀ j, β j) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F ω ∂(Measure.pi π) =
      ∫⁻ ω, ∫⁻ η, F (Function.update ω k η) ∂(π k) ∂(Measure.pi π) := by
  have hupd : Measurable (fun p : (∀ j, β j) × β k => Function.update p.1 k p.2) :=
    measurable_update'
  have hmap : Measure.map (fun p : (∀ j, β j) × β k => Function.update p.1 k p.2)
      ((Measure.pi π).prod (π k)) = Measure.pi π := by
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply hupd (MeasurableSet.univ_pi hs)]
    have hpre : (fun p : (∀ j, β j) × β k => Function.update p.1 k p.2) ⁻¹' (Set.pi Set.univ s)
        = (Set.pi Set.univ (Function.update s k Set.univ)) ×ˢ s k := by
      ext ⟨ω, η⟩
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
      constructor
      · intro h
        refine ⟨fun j => ?_, by simpa using h k⟩
        by_cases hj : j = k
        · subst hj; simp
        · have := h j
          simpa [Function.update_of_ne hj] using this
      · rintro ⟨h1, h2⟩ j
        by_cases hj : j = k
        · subst hj; simpa using h2
        · have := h1 j
          simpa [Function.update_of_ne hj] using this
    rw [hpre, Measure.prod_prod, Measure.pi_pi]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun j => π j (s j)) (Finset.mem_univ k)]
    have : ∏ j ∈ Finset.univ.erase k, π j (Function.update s k Set.univ j)
        = ∏ j ∈ Finset.univ.erase k, π j (s j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [this]
    simp [mul_comm]
  calc ∫⁻ ω, F ω ∂(Measure.pi π)
      = ∫⁻ ω, F ω ∂(Measure.map (fun p : (∀ j, β j) × β k => Function.update p.1 k p.2)
          ((Measure.pi π).prod (π k))) := by rw [hmap]
    _ = ∫⁻ p, F (Function.update p.1 k p.2) ∂((Measure.pi π).prod (π k)) :=
        lintegral_map hF hupd
    _ = _ := by
        exact lintegral_prod (fun p : (∀ j, β j) × β k => F (Function.update p.1 k p.2)) (hF.comp hupd).aemeasurable

end RobustShattering.Dev.L49

namespace RobustShattering.Supermartingale

theorem chk_lemma_4_9 {V : Type} [Fintype V] (G : SimpleGraph V) {T : ℕ}
    {Ω : V → Fin T → Type} [∀ u k, MeasurableSpace (Ω u k)]
    (μ : ∀ u k, Measure (Ω u k)) [∀ u k, IsProbabilityMeasure (μ u k)]
    (c : ℕ) (X Y : ℝ≥0) (hY : 0 < Y) (B : Randomness Ω → Set V)
    (γ : V → ℕ → Randomness Ω → ℝ≥0) (hγ : IsShatteringCost G c X Y μ B γ)
    (S : Finset V) (hS : LocalLLL.Main.separated G (2 * c) (S : Set V))
    (i : ℕ) (hi : i ≤ T) :
    ∫⁻ ω, ∏ v ∈ S, (γ v i ω : ℝ≥0∞) ∂(processMeasure μ) ≤ (X : ℝ≥0∞) ^ S.card := by
  classical
  induction i with
  | zero =>
    calc ∫⁻ ω, ∏ v ∈ S, (γ v 0 ω : ℝ≥0∞) ∂(processMeasure μ)
        ≤ ∫⁻ ω, (X : ℝ≥0∞) ^ S.card ∂(processMeasure μ) := by
          apply lintegral_mono
          intro ω
          calc ∏ v ∈ S, (γ v 0 ω : ℝ≥0∞) ≤ ∏ v ∈ S, (X : ℝ≥0∞) :=
                Finset.prod_le_prod' (fun v _ => by exact_mod_cast hγ.low_initial_cost v ω)
            _ = _ := Finset.prod_const _
      _ = (X : ℝ≥0∞) ^ S.card := by
          have : IsProbabilityMeasure (processMeasure μ) := by
            unfold processMeasure; infer_instance
          simp
  | succ i ih =>
    have hi' : i < T := hi
    have ih' := ih hi'.le
    have hF : Measurable (fun ω : Randomness Ω => ∏ v ∈ S, (γ v (i + 1) ω : ℝ≥0∞)) :=
      Finset.measurable_prod _ (fun v _ =>
        measurable_coe_nnreal_ennreal.comp (hγ.measurable v (i + 1) hi))
    have h1 := RobustShattering.Dev.L49.lintegral_update
      (fun k : Fin T => Measure.pi (fun u : V => μ u k)) ⟨i, hi'⟩ _ hF
    calc ∫⁻ ω, ∏ v ∈ S, (γ v (i + 1) ω : ℝ≥0∞) ∂(processMeasure μ)
        = ∫⁻ ω, ∫⁻ η, ∏ v ∈ S, (γ v (i + 1) (Function.update ω ⟨i, hi'⟩ η) : ℝ≥0∞)
            ∂(Measure.pi (fun u : V => μ u ⟨i, hi'⟩)) ∂(processMeasure μ) := h1
      _ ≤ ∫⁻ ω, ∏ v ∈ S, (γ v i ω : ℝ≥0∞) ∂(processMeasure μ) :=
          lintegral_mono (fun ω => lemma_4_8 G μ c X Y hY B γ hγ S hS i hi' ω)
      _ ≤ _ := ih'

end RobustShattering.Supermartingale
end

theorem solution : type_of% @RobustShattering.Supermartingale.chk_lemma_4_9 := @RobustShattering.Supermartingale.chk_lemma_4_9
