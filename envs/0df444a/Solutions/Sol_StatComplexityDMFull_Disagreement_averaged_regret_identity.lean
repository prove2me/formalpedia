-- Prove2me | solution 1 for StatComplexityDMFull.Disagreement.averaged_regret_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:58:50.066146+00:00
-- url     : https://prove2.me/submissions/fa1dc608-4349-4b9c-9cdb-da6fddd90d9d

import Mathlib
import Definitions.Def_StatComplexityDMFull_Disagreement_RadonLaw
import Definitions.Def_StatComplexityDMFull_Disagreement_MeanModel

set_option autoImplicit false

open MeasureTheory

open StatComplexityDMFull.Disagreement in
theorem solution {M A : Type*} [TopologicalSpace M] [DiscreteTopology M]
    [MeasurableSpace M] [BorelSpace M] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (μ : RadonLaw M) (D : MeanModel M A) (p : RadonLaw A) :
    (∫ m, (∫ a, D.mean m (D.optimal m) - D.mean m a ∂p.val) ∂μ.val) =
      ∫ n, (∫ m, (∫ a, D.mean m (D.optimal m) - D.mean n a ∂p.val) ∂μ.val) ∂μ.val := by
  haveI : DiscreteMeasurableSpace M := ⟨fun s => (isOpen_discrete s).measurableSet⟩
  have hbd : ∀ m a, ‖D.mean m a‖ ≤ 1 := by
    intro m a; rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(D.range m a).1, (D.range m a).2]
  have hiA : ∀ n, Integrable (D.mean n) p.val := fun n =>
    Integrable.of_bound (D.measurable n).aestronglyMeasurable 1 (Filter.Eventually.of_forall (hbd n))
  have hsplit : ∀ m n, ∫ a, D.mean m (D.optimal m) - D.mean n a ∂p.val =
      D.mean m (D.optimal m) - ∫ a, D.mean n a ∂p.val := by
    intro m n
    rw [integral_sub (integrable_const _) (hiA n), integral_const]
    simp
  simp_rw [hsplit]
  obtain ⟨G, hG⟩ : ∃ G : M → ℝ, G = fun n => ∫ a, D.mean n a ∂p.val := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : M → ℝ, c = fun m => D.mean m (D.optimal m) := ⟨_, rfl⟩
  have hGb : ∀ n, ‖G n‖ ≤ 1 := by
    intro n
    rw [hG]
    have := norm_integral_le_of_norm_le_const (μ := p.val) (C := 1)
      (Filter.Eventually.of_forall (hbd n))
    simpa using this
  have hGi : Integrable G μ.val :=
    Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hGb)
  have hci : Integrable c μ.val :=
    Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun m => by rw [hc]; exact hbd _ _))
  have e1 : ∀ m, D.mean m (D.optimal m) - ∫ a, D.mean m a ∂p.val = c m - G m := by
    intro m; rw [hc, hG]
  have e2 : ∀ m n, D.mean m (D.optimal m) - ∫ a, D.mean n a ∂p.val = c m - G n := by
    intro m n; rw [hc, hG]
  simp_rw [e1, e2]
  have e3 : ∀ n, ∫ m, (c m - G n) ∂μ.val = (∫ m, c m ∂μ.val) - G n := by
    intro n
    rw [integral_sub hci (integrable_const _), integral_const]
    simp
  simp_rw [e3]
  rw [integral_sub hci hGi, integral_sub (integrable_const _) hGi, integral_const]
  simp
