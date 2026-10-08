-- Prove2me | solution 1 for StabGen.Uniform.bounded_differences_empirical
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:49:21.396268+00:00
-- url     : https://prove2.me/submissions/d5bd4ce7-8f9f-4177-8378-a2870e500055

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

set_option autoImplicit false

open MeasureTheory FoundationsML.Stability in
theorem StabGenBD01f6_removeAt_replaceAt {Z : Type*} {m : ℕ} (S : Fin m → Z) (i : Fin m) (z' : Z) :
    StabGen.Hypothesis.removeAt (StabGen.Hypothesis.replaceAt S i z') i
      = StabGen.Hypothesis.removeAt S i := by
  unfold StabGen.Hypothesis.removeAt StabGen.Hypothesis.replaceAt
  apply Multiset.map_congr rfl
  intro j hj
  have hj' : j ≠ i := by
    have := Finset.mem_val.mp hj
    exact (Finset.mem_erase.mp this).1
  simp [Function.update_of_ne hj']

open MeasureTheory FoundationsML.Stability in
theorem StabGenBD01f6_gen_diff {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (h h' : X → Y') (M c : ℝ)
    (hf : Measurable (fun z => Loss L h z)) (hg : Measurable (fun z => Loss L h' z))
    (hfb : ∀ z, 0 ≤ Loss L h z ∧ Loss L h z ≤ M) (hgb : ∀ z, 0 ≤ Loss L h' z ∧ Loss L h' z ≤ M)
    (hp : ∀ z, |Loss L h z - Loss L h' z| ≤ c) :
    |GeneralizationError D L h - GeneralizationError D L h'| ≤ c := by
  unfold GeneralizationError
  have hfi : Integrable (fun z => Loss L h z) D :=
    Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hfb z).1, (hfb z).2])
  have hgi : Integrable (fun z => Loss L h' z) D :=
    Integrable.of_bound hg.aestronglyMeasurable M (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hgb z).1, (hgb z).2])
  rw [← integral_sub hfi hgi]
  have h1 : ∫ z, (Loss L h z - Loss L h' z) ∂D ≤ ∫ _z, c ∂D :=
    integral_mono (hfi.sub hgi) (integrable_const c) (fun z => (abs_le.mp (hp z)).2)
  have h2 : ∫ _z, (-c) ∂D ≤ ∫ z, (Loss L h z - Loss L h' z) ∂D :=
    integral_mono (integrable_const _) (hfi.sub hgi) (fun z => (abs_le.mp (hp z)).1)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1 h2
  rw [abs_le]; constructor <;> linarith

open MeasureTheory FoundationsML.Stability in
theorem StabGenBD01f6_emp_diff {X Y Y' : Type*} {m : ℕ} (L : Y' → Y → ℝ) (h h' : X → Y') (M c : ℝ)
    (S S' : Fin m → X × Y) (i : Fin m) (hS : ∀ j, j ≠ i → S' j = S j)
    (hfb : ∀ z, 0 ≤ Loss L h z ∧ Loss L h z ≤ M) (hgb : ∀ z, 0 ≤ Loss L h' z ∧ Loss L h' z ≤ M)
    (hp : ∀ z, |Loss L h z - Loss L h' z| ≤ c) :
    |EmpiricalError L S h - EmpiricalError L S' h'| ≤ c + M / m := by
  unfold EmpiricalError
  have hm : (0:ℝ) < m := by exact_mod_cast Fin.pos i
  have hterm : ∀ j, |Loss L h (S j) - Loss L h' (S' j)| ≤ c + (if j = i then M else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj
      have hc : 0 ≤ c := le_trans (abs_nonneg _) (hp (S j))
      rw [if_pos rfl, abs_le]
      constructor <;> linarith [(hfb (S j)).1, (hfb (S j)).2, (hgb (S' j)).1, (hgb (S' j)).2]
    · rw [if_neg hj, hS j hj, add_zero]
      exact hp (S j)
  have hsum : |∑ j, (Loss L h (S j) - Loss L h' (S' j))| ≤ ∑ j, (c + if j = i then M else 0) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
  have hsum2 : ∑ j : Fin m, (c + if j = i then M else 0) = m * c + M := by
    simp [Finset.sum_add_distrib]
  rw [hsum2] at hsum
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / m)]
  calc 1 / (m:ℝ) * |∑ j, (Loss L h (S j) - Loss L h' (S' j))| ≤ 1 / m * (m * c + M) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = c + M / m := by field_simp

open MeasureTheory FoundationsML.Stability in
theorem solution {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (M : ℝ)
    (hbound : ∀ (T : Multiset (X × Y)) (z : X × Y), 0 ≤ Loss L (A T) z ∧ Loss L (A T) z ≤ M)
    (m : ℕ) (β : ℝ) (hstab : StabGen.Uniform.HasUniformStability L A m β) :
    ∀ (S : Fin m → X × Y) (i : Fin m) (z' : X × Y),
      |(GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S)))
        - (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z')))
            - EmpiricalError L (StabGen.Hypothesis.replaceAt S i z') (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))))|
        ≤ 4 * β + M / m := by
  intro S i z'
  have hrem := StabGenBD01f6_removeAt_replaceAt S i z'
  have hp : ∀ z, |Loss L (A (StabGen.Hypothesis.trainingSet S)) z
      - Loss L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))) z| ≤ 2 * β := by
    intro z
    have h1 := hstab S i z
    have h2 := hstab (StabGen.Hypothesis.replaceAt S i z') i z
    rw [hrem] at h2
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hmeas : ∀ T : Fin m → X × Y,
      Measurable (fun z => Loss L (A (StabGen.Hypothesis.trainingSet T)) z) := by
    intro T
    exact (hA m).comp measurable_prodMk_left
  have hR := StabGenBD01f6_gen_diff D L (A (StabGen.Hypothesis.trainingSet S))
    (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))) M (2 * β)
    (hmeas S) (hmeas _) (hbound _) (hbound _) hp
  have hE := StabGenBD01f6_emp_diff L (A (StabGen.Hypothesis.trainingSet S))
    (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))) M (2 * β)
    S (StabGen.Hypothesis.replaceAt S i z') i
    (fun j hj => by simp [StabGen.Hypothesis.replaceAt, Function.update_of_ne hj])
    (hbound _) (hbound _) hp
  rw [abs_le] at hR hE ⊢
  constructor <;> linarith [hR.1, hR.2, hE.1, hE.2]
