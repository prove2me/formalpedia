-- Prove2me | solution 1 for PriceRobustness.Main.proposition_2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:42:17.00527+00:00
-- url     : https://prove2.me/submissions/a0fdfb8e-f0c6-4e9e-906f-76651719fdc2

import Definitions.Def_PriceRobustness_Main_RobustModel
import Definitions.Def_PriceRobustness_Main_Protection
import Definitions.Def_PriceRobustness_Main_Noise

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open PriceRobustness.Main

def lp0 : LinearProgram 1 2 where
  A := fun _ _ => 0
  b := fun _ => 10
  c := fun _ => 0
  lower := fun _ => 1
  upper := fun _ => 1

def model0 : RobustModel 1 2 where
  nominal := lp0
  J := fun _ => Finset.univ
  radius := fun _ j => if j = 0 then 1 else 2
  budget := fun _ => 0
  radius_nonneg := by
    intro i j _
    fin_cases j <;> norm_num
  budget_mem := by
    intro i
    simp

private lemma indep_on_unit {ι : Type} (P : Measure Unit) [IsProbabilityMeasure P]
    (η : ι → Unit → ℝ) : iIndepFun η P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S f _
  by_cases hne : ∀ i ∈ S, () ∈ η i ⁻¹' f i
  · have h1 : (⋂ i ∈ S, η i ⁻¹' f i) = Set.univ := by
      ext ⟨⟩
      simpa using hne
    have h2 : ∀ i ∈ S, P (η i ⁻¹' f i) = 1 := by
      intro i hi
      have hu : η i ⁻¹' f i = Set.univ := by
        ext ⟨⟩
        simpa using hne i hi
      rw [hu, measure_univ]
    rw [h1, measure_univ, Finset.prod_eq_one h2]
  · simp only [not_forall] at hne
    rcases hne with ⟨i0, hi0S, hi0⟩
    have h1 : (⋂ i ∈ S, η i ⁻¹' f i) = ∅ := by
      ext ⟨⟩
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨i0, hi0S, hi0⟩
    have h2 : P (η i0 ⁻¹' f i0) = 0 := by
      have he : η i0 ⁻¹' f i0 = ∅ := by
        ext ⟨⟩
        simpa using hi0
      rw [he, measure_empty]
    rw [h1, measure_empty, eq_comm]
    exact Finset.prod_eq_zero hi0S h2

theorem solution : ¬ (∀ {m N : ℕ} (D : RobustModel m N) (x : Fin N → ℝ) (hx : D.Optimal x) (i : Fin m) (S : Finset (Fin N)) (t r : Option (Fin N)) (hmax : MaximizesProtection (D.J i) (D.weight x i) (D.budget i) S t) (hmin : MinimizesSelected (D.weight x i) S t r) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (η : Fin N → Ω → ℝ) (hη : SymmetricNoise P (D.J i) η), (P.real {ω | (∑ j, D.uncertainEntry η i j ω * x j) > D.nominal.b i} ≤ P.real {ω | (∑ j ∈ D.J i, sourceGamma (D.weight x i) S r j * η j ω) ≥ D.budget i}) ∧ (∀ j ∈ D.J i, j ∉ S → sourceGamma (D.weight x i) S r j ≤ 1)) := by
  intro H
  let x0 : Fin 2 → ℝ := fun _ => 1
  have hx0 : model0.Optimal x0 := by
    refine ⟨⟨fun _ => 1, fun _ => 0, fun _ j => if j = 0 then 1 else 2, ?_⟩, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        simp [model0, lp0, Fin.sum_univ_two]
        norm_num
      · intro i j _
        fin_cases j <;> simp [model0]
      · intro j
        simp [x0]
      · intro j
        simp [model0, lp0, x0]
      · intro i j _
        fin_cases j <;> norm_num
      · intro j
        norm_num
      · intro i
        norm_num
    · intro x' y z p _
      simp [LinearProgram.objective, model0, lp0]
  have hmax : MaximizesProtection (model0.J 0) (model0.weight x0 0) (model0.budget 0) ∅ (some 0) := by
    refine ⟨?_, ?_⟩
    · simp [AdmissibleProtection, model0]
    · intro S' t' hadm
      have hcard : S' = ∅ := by
        simp [AdmissibleProtection, model0] at hadm
        exact hadm.1
      subst hcard
      simp [protectionValue, model0]
  have hmin : MinimizesSelected (model0.weight x0 0) ∅ (some 0) (some 0) := by
    refine ⟨0, rfl, by simp, ?_⟩
    intro l hl
    simp at hl
    subst hl
    rfl
  let P0 : Measure Unit := Measure.dirac ()
  let η0 : Fin 2 → Unit → ℝ := fun _ _ => 0
  have hη0 : SymmetricNoise P0 (model0.J 0) η0 := by
    refine ⟨?_, ?_, ?_, indep_on_unit P0 (fun j : model0.J 0 => η0 j.val)⟩
    · intro j _
      exact measurable_const
    · intro j _ ω
      simp [η0]
    · intro j _
      have hneg : (fun ω : Unit => -η0 j ω) = η0 j := by
        ext ω
        simp [η0]
      rw [hneg]
      exact IdentDistrib.refl measurable_const.aemeasurable
  have hconc := (H model0 x0 hx0 0 ∅ (some 0) (some 0) hmax hmin P0 η0 hη0).2
  have h1 := hconc 1 (by simp [model0]) (by simp)
  simp [sourceGamma, RobustModel.weight, model0, x0] at h1
