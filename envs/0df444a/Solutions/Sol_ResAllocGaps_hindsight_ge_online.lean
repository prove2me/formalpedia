-- Prove2me | solution 1 for ResAllocGaps.hindsight_ge_online
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T00:17:38.3538+00:00
-- url     : https://prove2.me/submissions/a5e49758-b2b8-4f6d-851e-7eabb7d2428a

import Mathlib
import Definitions.Def_ResAllocGaps_OnlinePolicy

set_option autoImplicit false

open MeasureTheory ResAllocGaps

theorem ResAllocGaps.measurable_sup'_eval {δ ι : Type*} [MeasurableSpace δ] (f : ι → δ → ℝ)
    {s : Finset ι} (H : s.Nonempty) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun x => s.sup' H (fun i => f i x)) := by
  induction H using Finset.Nonempty.cons_induction with
  | singleton a =>
    simp only [Finset.sup'_singleton]
    exact hf a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    simp only [Finset.sup'_cons hs]
    exact (hf a (Finset.mem_cons_self a s)).sup
      (ih (fun i hi => hf i (Finset.mem_cons_of_mem hi)))

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Icc 0 1) = 1)
    (T B : ℕ) (π : OnlinePolicy μ T B) :
    (∀ᵐ ω ∂(sampleLaw μ T), π.reward ω ≤ hsValue T B (abilities ω)) ∧
      ∫ ω, π.reward ω ∂(sampleLaw μ T) ≤ ∫ ω, hsValue T B (abilities ω) ∂(sampleLaw μ T) := by
  haveI : IsProbabilityMeasure seedLaw := ⟨by
    simp [seedLaw, Measure.restrict_apply MeasurableSet.univ, Real.volume_Icc]⟩
  haveI : IsProbabilityMeasure (sampleLaw μ T) := by
    unfold sampleLaw
    infer_instance
  have hemp : (∅ : Finset (Fin T)) ∈ (Finset.univ : Finset (Finset (Fin T))).filter
      (fun S => S.card ≤ B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Finset.card_empty]; exact Nat.zero_le B⟩
  have hμae : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1 :=
    ae_iff.mpr ((prob_compl_eq_zero_iff measurableSet_Icc).mpr hμ)
  have hprod : ∀ᵐ p ∂(μ.prod seedLaw), p.1 ∈ Set.Icc (0 : ℝ) 1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae hμae
  have hθ : ∀ᵐ ω ∂(sampleLaw μ T), ∀ t, (ω t).1 ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro t
    exact (measurePreserving_eval (fun _ : Fin T => μ.prod seedLaw) t).quasiMeasurePreserving.ae
      hprod
  have hs_nonneg : ∀ θ : Fin T → ℝ, 0 ≤ hsValue T B θ := fun θ =>
    Finset.le_sup'_of_le _ hemp (by simp)
  have hsMeas : Measurable (fun ω : Sample T => hsValue T B (abilities ω)) := by
    unfold hsValue abilities
    exact ResAllocGaps.measurable_sup'_eval (fun S (ω : Sample T) => ∑ t ∈ S, (ω t).1) _
      (fun S _ => Finset.measurable_sum S (fun t _ => measurable_fst.comp (measurable_pi_apply t)))
  have hsInt : Integrable (fun ω => hsValue T B (abilities ω)) (sampleLaw μ T) := by
    apply Integrable.of_bound hsMeas.aestronglyMeasurable T
    filter_upwards [hθ] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hs_nonneg _)]
    unfold hsValue
    apply Finset.sup'_le
    intro S _
    calc ∑ t ∈ S, abilities ω t ≤ ∑ t ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum (fun t _ => (hω t).2)
      _ = S.card := by simp
      _ ≤ T := by
          have := Finset.card_le_univ S
          simp only [Fintype.card_fin] at this
          exact_mod_cast this
  have part1 : ∀ᵐ ω ∂(sampleLaw μ T), π.reward ω ≤ hsValue T B (abilities ω) := by
    filter_upwards [π.budget_ae] with ω hω
    have hrew : π.reward ω =
        ∑ t ∈ Finset.univ.filter (fun t => π.accept t (obsPrefix ω t) = true), (ω t).1 := by
      rw [Finset.sum_filter]
      rfl
    rw [hrew]
    unfold hsValue
    exact Finset.le_sup' (fun S => ∑ t ∈ S, abilities ω t)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω⟩)
  refine ⟨part1, ?_⟩
  by_cases hint : Integrable (fun ω => π.reward ω) (sampleLaw μ T)
  · exact integral_mono_ae hint hsInt part1
  · rw [integral_undef hint]
    exact integral_nonneg (fun ω => hs_nonneg _)
