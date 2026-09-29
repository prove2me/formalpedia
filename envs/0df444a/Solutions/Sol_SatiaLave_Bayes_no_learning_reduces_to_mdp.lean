-- Prove2me | solution 1 for SatiaLave.Bayes.no_learning_reduces_to_mdp
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:00:50.11926+00:00
-- url     : https://prove2.me/submissions/e9caac1a-e8e5-4b3d-aece-dbf6effeec14

import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory

namespace SatiaLave.Bayes

theorem aux_nlr_pbar_dirac {S : Type*} [Fintype S] {D : S → Type*} [∀ i, Fintype (D i)]
    (P : Mat S D) (l : S) (m : D l) (j : S) :
    pbar (Measure.dirac P) l m j = P l m j := by
  unfold pbar
  exact integral_dirac' _ _ (by fun_prop : Measurable fun Q : Mat S D => Q l m j).stronglyMeasurable

theorem aux_nlr_bayes_dirac {S : Type*} [Fintype S] {D : S → Type*} [∀ i, Fintype (D i)]
    (P : Mat S D) (hP : ∀ i k j, 0 ≤ P i k j) (l : S) (m : D l) (j : S) :
    bayes (Measure.dirac P) l m j = Measure.dirac P := by
  unfold bayes
  rw [aux_nlr_pbar_dirac]
  split_ifs with h
  · rfl
  · rw [dirac_withDensity' (by fun_prop : Measurable fun Q : Mat S D => ENNReal.ofReal (Q l m j)),
      smul_smul]
    have hpos : 0 < P l m j := lt_of_le_of_ne (hP l m j) (Ne.symm h)
    rw [ENNReal.inv_mul_cancel (by simpa using hpos) ENNReal.ofReal_ne_top, one_smul]

end SatiaLave.Bayes

open SatiaLave.Bayes
open MeasureTheory

theorem solution {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D)
    (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f)
    (P : Mat S D) (hP : IsStoch P) :
    (∀ (l : S) (m : D l) (j : S), bayes (Measure.dirac P) l m j = Measure.dirac P) ∧
    SolvesKnown M P (fun i => f i (Measure.dirac P)) := by
  have hnn : ∀ i k j, 0 ≤ P i k j := fun i k j => (hP i k).1 j
  have hB := aux_nlr_bayes_dirac P hnn
  refine ⟨hB, ?_⟩
  have hprior : IsPrior (Measure.dirac P) := by
    refine ⟨inferInstance, ?_⟩
    rw [Measure.dirac_apply]
    simp [hP]
  intro i
  beta_reduce
  rw [hf i _ hprior]
  congr 1
  funext k
  simp only [aux_nlr_pbar_dirac, hB]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring
