-- Prove2me | solution 1 for SupportVectorMachines.Calibration.lemma_3_11_existence_of_approximate_minimizers
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:15:17.127743+00:00
-- url     : https://prove2.me/submissions/6d1ac59b-2b94-4ca2-bf92-411eb6025051

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace

set_option autoImplicit false

namespace Cex742131c3

open MeasureTheory SupportVectorMachines.Calibration

/-- `Bool` carrying the trivial σ-algebra `{∅, univ}`. -/
def TB : Type := Bool

instance instMS : MeasurableSpace TB := ⊥

def tt : TB := (true : Bool)
def ff : TB := (false : Bool)

theorem tt_ne_ff : tt ≠ ff := by
  intro h
  exact Bool.noConfusion h

theorem measurableSet_TB (s : Set TB) (hs : MeasurableSet s) : s = ∅ ∨ s = Set.univ :=
  MeasurableSpace.measurableSet_bot_iff.mp hs

/-- The trivial σ-algebra is complete for any probability measure. -/
theorem complete_TB : IsCompleteMeasurableSpace TB := by
  refine ⟨Measure.dirac tt, inferInstance, ?_⟩
  rintro s ⟨t, ht, h0, hst⟩
  rcases measurableSet_TB t ht with rfl | rfl
  · rw [Set.subset_empty_iff.mp hst]; exact MeasurableSet.empty
  · simp at h0

/-- Under the trivial σ-algebra a probability-a.e. statement holds everywhere. -/
theorem ae_TB (μ : Measure TB) [IsProbabilityMeasure μ] (p : TB → Prop)
    (h : ∀ᵐ x ∂μ, p x) (x : TB) : p x := by
  rw [ae_iff] at h
  obtain ⟨t, hst, ht, h0⟩ := exists_measurable_superset_of_null h
  by_contra hx
  rcases measurableSet_TB t ht with rfl | rfl
  · exact (hst hx : x ∈ (∅ : Set TB))
  · simp at h0

/-- A measurable real function on the trivial σ-algebra is constant. -/
theorem measurable_TB (f : TB → ℝ) (hf : Measurable f) (a b : TB) : f a = f b := by
  have hm : MeasurableSet (f ⁻¹' {f a}) := hf (measurableSet_singleton (f a))
  rcases measurableSet_TB _ hm with h | h
  · have : a ∈ f ⁻¹' {f a} := rfl
    rw [h] at this
    exact absurd this (Set.notMem_empty a)
  · have : b ∈ f ⁻¹' {f a} := by rw [h]; trivial
    exact (this : f b = f a).symm

open Classical in
/-- The required exact selection `tt ↦ 1, ff ↦ 0`. -/
noncomputable def g (x : TB) : ℝ := if x = tt then 1 else 0

open Classical in
/-- Loss that is `0` exactly at `t = g x`, else `1`. -/
noncomputable def L : Loss TB := fun x _ t => if t = g x then 0 else 1

theorem innerRisk_eq (x : TB) (t : ℝ) :
    innerRisk L (Measure.dirac (0 : ℝ)) x t = ENNReal.ofReal (L x 0 t) := by
  unfold innerRisk
  simp [lintegral_dirac]

theorem minInnerRisk_eq (x : TB) : minInnerRisk L (Measure.dirac (0 : ℝ)) x = 0 := by
  refine le_antisymm ?_ (by simp)
  refine (iInf_le _ (g x)).trans ?_
  rw [innerRisk_eq]
  simp [L]

theorem mem_approx (x : TB) (t : ℝ)
    (ht : t ∈ approxMinimizers L (Measure.dirac (0 : ℝ)) x 1) : t = g x := by
  unfold approxMinimizers at ht
  simp only [Set.mem_ofPred_eq] at ht
  rw [innerRisk_eq, minInnerRisk_eq, zero_add] at ht
  by_contra hne
  simp [L, hne] at ht

end Cex742131c3

open MeasureTheory SupportVectorMachines.Calibration in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (L : Loss X)
    (PX : Measure X) [IsProbabilityMeasure PX] (κ : X → Measure ℝ) (hκ : Measurable κ)
    (hκprob : ∀ x, IsProbabilityMeasure (κ x))
    (ε : ENNReal) (hε : 0 < ε),
    (∀ᵐ x ∂PX, minInnerRisk L (κ x) x < ⊤) ↔
      ∃ f : X → ℝ, Measurable f ∧ ∀ᵐ x ∂PX, f x ∈ approxMinimizers L (κ x) x ε) := by
  intro h
  have key := @h Cex742131c3.TB Cex742131c3.instMS Cex742131c3.complete_TB Cex742131c3.L
    (Measure.dirac Cex742131c3.tt) inferInstance (fun _ => Measure.dirac (0 : ℝ))
    measurable_const (fun _ => inferInstance) 1 one_pos
  have lhs : ∀ᵐ x ∂(Measure.dirac Cex742131c3.tt : Measure Cex742131c3.TB),
      minInnerRisk Cex742131c3.L (Measure.dirac (0 : ℝ)) x < ⊤ :=
    Filter.Eventually.of_forall (fun x => by
      rw [Cex742131c3.minInnerRisk_eq]; exact ENNReal.zero_lt_top)
  obtain ⟨f, hf, hae⟩ := key.mp lhs
  have hall := Cex742131c3.ae_TB _ _ hae
  have h1 := Cex742131c3.mem_approx _ _ (hall Cex742131c3.tt)
  have h0 := Cex742131c3.mem_approx _ _ (hall Cex742131c3.ff)
  have hc := Cex742131c3.measurable_TB f hf Cex742131c3.tt Cex742131c3.ff
  rw [h1, h0] at hc
  simp [Cex742131c3.g, Cex742131c3.tt_ne_ff.symm] at hc
