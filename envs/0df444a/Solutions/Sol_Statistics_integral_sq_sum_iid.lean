-- Prove2me | solution 1 for Statistics.integral_sq_sum_iid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-22T15:22:25.266687+00:00
-- url     : https://prove2.me/submissions/a10ed1b1-07cf-4ff9-a236-5b8514c0d33e

import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

-- === iid_sum.lean ===




namespace Statistics

variable {Ω : Type*} [MeasurableSpace Ω]

lemma memLp_eval (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (φ : Ω → ℝ)
    (hφ : MemLp φ 2 μ) (i : Fin T) :
    MemLp (fun path : Fin T → Ω => φ (path i)) 2 (Measure.pi fun _ : Fin T => μ) := by
  have hmap : Measure.map (fun path : Fin T → Ω => path i)
      (Measure.pi fun _ : Fin T => μ) = μ := (measurePreserving_eval _ i).map_eq
  have h : MemLp φ 2 (Measure.map (fun path : Fin T → Ω => path i)
      (Measure.pi fun _ : Fin T => μ)) := by rw [hmap]; exact hφ
  exact (memLp_map_measure_iff h.1 (measurable_pi_apply i).aemeasurable).1 h

lemma integral_eval (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (i : Fin T) :
    ∫ path, f (path i) ∂(Measure.pi fun _ : Fin T => μ) = ∫ x, f x ∂μ := by
  have hmap : Measure.map (fun path : Fin T → Ω => path i)
      (Measure.pi fun _ : Fin T => μ) = μ := (measurePreserving_eval _ i).map_eq
  have h := integral_map (μ := Measure.pi fun _ : Fin T => μ)
    (φ := fun path : Fin T → Ω => path i) (f := f)
    (measurable_pi_apply i).aemeasurable (by rw [hmap]; exact hf)
  rw [hmap] at h
  exact h.symm

/-- **The second moment of the sum of a centred functional over an i.i.d. sample** is `T`
times the one-observation second moment. -/
theorem integral_sq_sum_iid_aux (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (φ : Ω → ℝ)
    (hmeas : Measurable φ) (hφ : MemLp φ 2 μ) (hφ0 : ∫ x, φ x ∂μ = 0) :
    ∫ path, (∑ i : Fin T, φ (path i)) ^ 2 ∂(Measure.pi fun _ : Fin T => μ)
      = (T : ℝ) * ∫ x, (φ x) ^ 2 ∂μ := by
  classical
  set P : Measure (Fin T → Ω) := Measure.pi fun _ : Fin T => μ with hPdef
  have hL2 : ∀ i : Fin T, MemLp (fun path : Fin T → Ω => φ (path i)) 2 P :=
    fun i => memLp_eval μ T φ hφ i
  have hindep : iIndepFun (fun (i : Fin T) (path : Fin T → Ω) => path i) P :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have hprod : ∀ i j : Fin T, Integrable (fun path : Fin T → Ω =>
      φ (path i) * φ (path j)) P := fun i j => (hL2 i).integrable_mul (hL2 j)
  have hcross : ∀ i j : Fin T, i ≠ j →
      ∫ path, φ (path i) * φ (path j) ∂P = 0 := by
    intro i j hij
    have hI : IndepFun (fun path : Fin T → Ω => φ (path i))
        (fun path : Fin T → Ω => φ (path j)) P :=
      (hindep.indepFun hij).comp hmeas hmeas
    have hmul := hI.integral_mul_eq_mul_integral (hL2 i).1 (hL2 j).1
    simp only [Pi.mul_apply] at hmul
    rw [hmul, integral_eval μ T hφ.1 i, hφ0, zero_mul]
  have hdiag : ∀ i : Fin T, ∫ path, φ (path i) * φ (path i) ∂P
      = ∫ x, (φ x) ^ 2 ∂μ := by
    intro i
    have h := integral_eval μ T (f := fun x => (φ x) ^ 2)
      (hmeas.pow_const 2).aestronglyMeasurable i
    simpa [sq] using h
  have hexp : ∀ path : Fin T → Ω, (∑ i : Fin T, φ (path i)) ^ 2
      = ∑ i : Fin T, ∑ j : Fin T, φ (path i) * φ (path j) := by
    intro path; rw [sq, Finset.sum_mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  rw [integral_finsetSum (μ := P) (f := fun (i : Fin T) (path : Fin T → Ω) =>
      ∑ j : Fin T, φ (path i) * φ (path j)) _
    (fun i _ => integrable_finsetSum (μ := P) (f := fun (j : Fin T) (path : Fin T → Ω) =>
      φ (path i) * φ (path j)) _ (fun j _ => hprod i j))]
  have hrow : ∀ i : Fin T, ∫ path, (∑ j : Fin T, φ (path i) * φ (path j)) ∂P
      = ∫ x, (φ x) ^ 2 ∂μ := by
    intro i
    rw [integral_finsetSum (μ := P) (f := fun (j : Fin T) (path : Fin T → Ω) =>
      φ (path i) * φ (path j)) _ (fun j _ => hprod i j)]
    rw [Finset.sum_eq_single i (fun j _ hj => hcross i j (Ne.symm hj))
      (fun h => absurd (Finset.mem_univ i) h)]
    exact hdiag i
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- The sum of a centred functional over an i.i.d. sample is centred. -/
theorem integral_sum_iid (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (φ : Ω → ℝ)
    (hφ : Integrable φ μ) (hφ0 : ∫ x, φ x ∂μ = 0) :
    ∫ path, (∑ i : Fin T, φ (path i)) ∂(Measure.pi fun _ : Fin T => μ) = 0 := by
  classical
  set P : Measure (Fin T → Ω) := Measure.pi fun _ : Fin T => μ with hPdef
  have hint : ∀ i : Fin T, Integrable (fun path : Fin T → Ω => φ (path i)) P := by
    intro i
    have hmap : Measure.map (fun path : Fin T → Ω => path i) P = μ :=
      (measurePreserving_eval _ i).map_eq
    have h : Integrable φ (Measure.map (fun path : Fin T → Ω => path i) P) := by
      rw [hmap]; exact hφ
    exact (integrable_map_measure h.1 (measurable_pi_apply i).aemeasurable).1 h
  rw [integral_finsetSum (μ := P) (f := fun (i : Fin T) (path : Fin T → Ω) => φ (path i)) _
    (fun i _ => hint i)]
  exact Finset.sum_eq_zero fun i _ => by rw [integral_eval μ T hφ.1 i, hφ0]

end Statistics


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : ℕ) (φ : Ω → ℝ)
    (hmeas : Measurable φ) (hφ : MemLp φ 2 μ) (hφ0 : ∫ x, φ x ∂μ = 0) :
    ∫ path, (∑ i : Fin T, φ (path i)) ^ 2 ∂(Measure.pi fun _ : Fin T => μ)
      = (T : ℝ) * ∫ x, (φ x) ^ 2 ∂μ :=
  Statistics.integral_sq_sum_iid_aux μ T φ hmeas hφ hφ0
