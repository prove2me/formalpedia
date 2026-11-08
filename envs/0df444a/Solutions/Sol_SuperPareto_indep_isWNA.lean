-- Prove2me | solution 1 for SuperPareto.indep_isWNA
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:46:47.603447+00:00
-- url     : https://prove2.me/submissions/522f2f89-f7a6-4ee7-aaa8-8575a04038a0

import Mathlib
import Definitions.Def_SuperPareto_IsWNA

open MeasureTheory ProbabilityTheory

open SuperPareto in
theorem solution {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [Fintype ι] (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) :
    IsWNA P X := by
  classical
  intro i S hS _ x
  set A : Finset ι := Finset.univ \ {i} with hA
  set B : Finset ι := {i} with hB
  have hAB : Disjoint A B := by
    rw [hA, hB]; exact Finset.sdiff_disjoint
  have hI := hind.indepFun_finset A B hAB hX
  have hmemA : ∀ j : {j // j ≠ i}, j.1 ∈ A := by
    intro j; rw [hA, hB]; simp [j.2]
  set φ : (A → ℝ) → ({j // j ≠ i} → ℝ) := fun y j => y ⟨j.1, hmemA j⟩ with hφ
  set ψ : (B → ℝ) → ℝ := fun y => y ⟨i, by rw [hB]; exact Finset.mem_singleton_self i⟩ with hψ
  have hφm : Measurable φ := by
    apply measurable_pi_lambda
    intro j
    exact measurable_pi_apply _
  have hψm : Measurable ψ := measurable_pi_apply _
  have hI2 := hI.comp hφm hψm
  have key := hI2.measure_inter_preimage_eq_mul S (Set.Iic x) hS measurableSet_Iic
  have e1 : {ω | (fun j : {j // j ≠ i} => X j ω) ∈ S ∧ X i ω ≤ x} =
      (φ ∘ fun ω (j : A) => X j ω) ⁻¹' S ∩ (ψ ∘ fun ω (j : B) => X j ω) ⁻¹' Set.Iic x := by
    ext ω; simp [hφ, hψ]
  have e2 : {ω | (fun j : {j // j ≠ i} => X j ω) ∈ S} = (φ ∘ fun ω (j : A) => X j ω) ⁻¹' S := by
    ext ω; simp [hφ]
  have e3 : {ω | X i ω ≤ x} = (ψ ∘ fun ω (j : B) => X j ω) ⁻¹' Set.Iic x := by
    ext ω; simp [hψ]
  rw [e1, e2, e3, key]
