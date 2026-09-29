-- Prove2me | solution 1 for StochasticOrders.PositiveDependence.supermodular_order_closure_properties
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T05:14:50.148516+00:00
-- url     : https://prove2.me/submissions/9cca79d4-a114-4ab9-ba86-25da54666105

import Mathlib
import Definitions.Def_StochasticOrders_PositiveDependence_Orders

set_option autoImplicit false

open MeasureTheory StochasticOrders.PositiveDependence Supermodularity.Monotonicity in
theorem sm_pushforward_aux {ι κ : Type*} [Fintype ι] [Fintype κ] (P Q : Measure (ι → ℝ))
    (G : (ι → ℝ) → (κ → ℝ)) (hG : Measurable G)
    (hsm : ∀ φ : (κ → ℝ) → ℝ, SupermodularOn φ Set.univ → SupermodularOn (φ ∘ G) Set.univ)
    (h : SupermodularOrder P Q) :
    SupermodularOrder (Measure.map G P) (Measure.map G Q) := by
  intro φ hφ hiP hiQ
  rw [integral_map hG.aemeasurable hiP.aestronglyMeasurable,
    integral_map hG.aemeasurable hiQ.aestronglyMeasurable]
  exact h (φ ∘ G) (hsm φ hφ) ((integrable_map_measure hiP.1 hG.aemeasurable).1 hiP)
    ((integrable_map_measure hiQ.1 hG.aemeasurable).1 hiQ)

open MeasureTheory StochasticOrders.PositiveDependence Supermodularity.Monotonicity in
theorem solution {n : ℕ} (P Q : Measure (Fin n → ℝ)) :
    (∀ g : Fin n → ℝ → ℝ, ((∀ i, Monotone (g i)) ∨ (∀ i, Antitone (g i))) →
      (∀ i, Measurable (g i)) →
      SupermodularOrder P Q →
      SupermodularOrder (Measure.map (fun x i => g i (x i)) P)
        (Measure.map (fun x i => g i (x i)) Q)) ∧
    (∀ (I : Set (Fin n)) [DecidablePred (· ∈ I)],
      SupermodularOrder P Q →
      SupermodularOrder (Measure.map (fun x : Fin n → ℝ => fun i : {i // i ∈ I} => x i) P)
        (Measure.map (fun x : Fin n → ℝ => fun i : {i // i ∈ I} => x i) Q)) := by
  refine ⟨?_, ?_⟩
  · intro g hmono hmeas h
    refine sm_pushforward_aux P Q _ (measurable_pi_lambda _ fun i =>
      (hmeas i).comp (measurable_pi_apply i)) ?_ h
    intro φ hφ x _ y _
    rcases hmono with hm | ha
    · have h1 : (fun i => g i ((x ⊔ y) i)) = (fun i => g i (x i)) ⊔ (fun i => g i (y i)) := by
        funext i
        simp only [Pi.sup_apply]
        exact (hm i).map_max
      have h2 : (fun i => g i ((x ⊓ y) i)) = (fun i => g i (x i)) ⊓ (fun i => g i (y i)) := by
        funext i
        simp only [Pi.inf_apply]
        exact (hm i).map_min
      simp only [Function.comp_apply]
      rw [h1, h2]
      exact hφ (Set.mem_univ _) (Set.mem_univ _)
    · have h1 : (fun i => g i ((x ⊔ y) i)) = (fun i => g i (x i)) ⊓ (fun i => g i (y i)) := by
        funext i
        simp only [Pi.sup_apply, Pi.inf_apply]
        exact (ha i).map_max
      have h2 : (fun i => g i ((x ⊓ y) i)) = (fun i => g i (x i)) ⊔ (fun i => g i (y i)) := by
        funext i
        simp only [Pi.inf_apply, Pi.sup_apply]
        exact (ha i).map_min
      simp only [Function.comp_apply]
      rw [h1, h2, add_comm (φ _) (φ ((fun i => g i (x i)) ⊔ (fun i => g i (y i))))]
      exact hφ (Set.mem_univ _) (Set.mem_univ _)
  · intro I _ h
    refine sm_pushforward_aux P Q _ (measurable_pi_lambda _ fun i =>
      measurable_pi_apply _) ?_ h
    intro φ hφ x _ y _
    exact hφ (Set.mem_univ _) (Set.mem_univ _)
