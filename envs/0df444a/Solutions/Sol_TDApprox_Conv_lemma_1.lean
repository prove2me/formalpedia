-- Prove2me | solution 1 for TDApprox.Conv.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T12:51:18.617731+00:00
-- url     : https://prove2.me/submissions/c458a852-a7ad-49a2-a59e-2285332b64c3

import Mathlib
import Definitions.Def_TDApprox_Conv_Model

open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open TDApprox.Conv

set_option autoImplicit false

namespace MarkovL2Proof

lemma weighted_sq_iff {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [Countable S] (π : Measure S) [IsProbabilityMeasure π] (J : S → ℝ) :
    Integrable (fun i => J i ^ 2) π ↔ MemL2D π J := by
  have h := integrable_sum_dirac_iff (f := fun i => J i ^ 2) (x := id)
    (c := fun i => π {i}) (fun i => measure_ne_top π {i})
  simpa [Measure.sum_smul_dirac, MemL2D, Real.norm_eq_abs, abs_sq] using h

lemma integral_sq_eq_sum {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [Countable S] (π : Measure S) (J : S → ℝ) (hJ : Integrable (fun i => J i ^ 2) π) :
    (∫ i, J i ^ 2 ∂π) = ∑' i, (π {i}).toReal * J i ^ 2 := by
  simpa [Measure.real, smul_eq_mul] using integral_countable hJ

end MarkovL2Proof

theorem solution {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (h1a : Assumption1a P π) (J : S → ℝ) (hJ : MemL2D π J) :
    (∀ i, Integrable J (P i)) ∧ MemL2D π (Pop P J) ∧ normD π (Pop P J) ≤ normD π J := by
  have hj2 : Integrable (fun i => J i ^ 2) π := (MarkovL2Proof.weighted_sq_iff π J).mpr hJ
  have hstat : P ∘ₘ π = π := h1a.invariant
  have hcomp : Integrable (fun i => J i ^ 2) (P ∘ₘ π) := by rwa [hstat]
  have hae : ∀ᵐ i ∂π, Integrable (fun j => J j ^ 2) (P i) :=
    Measure.ae_integrable_of_integrable_comp hcomp
  have hrow2 : ∀ i, Integrable (fun j => J j ^ 2) (P i) := by
    intro i
    exact (ae_iff_of_countable.mp hae) i (ne_of_gt (h1a.pos i))
  have hrowLp : ∀ i, MemLp J 2 (P i) := by
    intro i
    exact (memLp_two_iff_integrable_sq (measurable_of_countable J).aestronglyMeasurable).mpr (hrow2 i)
  have hrow : ∀ i, Integrable J (P i) := fun i => (hrowLp i).integrable (by norm_num)
  have hbound : ∀ i, (Pop P J i) ^ 2 ≤ ∫ j, J j ^ 2 ∂P i := by
    intro i
    have h := variance_nonneg J (P i)
    rw [variance_eq_sub (hrowLp i)] at h
    exact sub_nonneg.mp h
  have houter : Integrable (fun i => ∫ j, J j ^ 2 ∂P i) π := by
    have h := Measure.integrable_integral_norm_of_integrable_comp hcomp
    simpa only [Real.norm_eq_abs, abs_sq] using h
  have hpj2 : Integrable (fun i => (Pop P J i) ^ 2) π := by
    exact houter.mono_nonneg (measurable_of_countable _).aestronglyMeasurable
      (ae_of_all _ fun i => sq_nonneg _) (ae_of_all _ hbound)
  have hiter : (∫ i, ∫ j, J j ^ 2 ∂P i ∂π) = ∫ j, J j ^ 2 ∂π := by
    have hk : Integrable (fun i => J i ^ 2) ((P ∘ₖ Kernel.const Unit π) ()) := by
      simpa only [← Measure.comp_eq_comp_const_apply] using hcomp
    have h := Kernel.integral_comp hk
    simpa only [Kernel.comp_apply, Kernel.const_apply, h1a.invariant.def] using h.symm
  refine ⟨hrow, (MarkovL2Proof.weighted_sq_iff π (Pop P J)).mp hpj2, ?_⟩
  apply Real.sqrt_le_sqrt
  rw [← MarkovL2Proof.integral_sq_eq_sum π (Pop P J) hpj2,
    ← MarkovL2Proof.integral_sq_eq_sum π J hj2, ← hiter]
  exact integral_mono hpj2 houter hbound

#print axioms solution
