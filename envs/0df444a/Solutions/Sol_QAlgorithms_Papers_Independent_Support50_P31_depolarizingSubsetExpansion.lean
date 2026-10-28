-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P31.depolarizingSubsetExpansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:18:03.600401+00:00
-- url     : https://prove2.me/submissions/fddfebdc-9914-4900-8578-a0f3e3cbe780

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

namespace X6DE

lemma prod_ite_split {n : ℕ} (t : Finset (Fin n)) (a b : Fin n → ℂ) :
    (∏ j, if j ∈ t then a j else b j) = (∏ j ∈ t, a j) * ∏ j ∈ Finset.univ \ t, b j := by
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext j; simp
  · congr 1; ext j; simp

lemma key {n : ℕ} (p : Fin n → ℝ) (u v : Fin n → ℂ) :
    ∏ j, ((p j : ℂ) * u j + ((1 - p j : ℝ) : ℂ) * v j) =
      ∑ L : Finset (Fin n), ((∏ j, if j ∈ L then p j else 1 - p j : ℝ) : ℂ) *
        ∏ j, (if j ∈ L then u j else v j) := by
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  push_cast
  rw [← Finset.prod_mul_distrib]
  have : ∀ j, ((if j ∈ t then (p j : ℂ) else ((1 : ℂ) - p j)) *
      (if j ∈ t then u j else v j)) =
      if j ∈ t then (p j : ℂ) * u j else ((1 : ℂ) - p j) * v j := by
    intro j; split_ifs <;> rfl
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_sub, Complex.ofReal_one, this]
  rw [prod_ite_split]

end X6DE

open QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P31
open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

theorem solution {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (X : Matrix ((i : Fin n) → Fin (d i)) ((i : Fin n) → Fin (d i)) ℂ) :
    depolarizingProduct d hd p X =
      ∑ L : Finset (Fin n), (depolarizingSubsetCoefficient p L : ℂ) • subsetExpectation d hd L X := by
  ext y y'
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  unfold depolarizingProduct subsetExpectation tensorChannels
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  have gen : ∀ M : (j : Fin n) → Matrix (Fin (d j)) (Fin (d j)) ℂ,
      ∏ j, QuditFidelity.depolarizingMap (d j) (hd j) (p j) (M j) (y j) (y' j) =
      ∑ L : Finset (Fin n), (depolarizingSubsetCoefficient p L : ℂ) *
        ∏ j, (if j ∈ L then QuditFidelity.depolarizingMap (d j) (hd j) 1 else id)
          (M j) (y j) (y' j) := by
    intro M
    have hF : ∀ j, QuditFidelity.depolarizingMap (d j) (hd j) (p j) (M j) (y j) (y' j) =
        (p j : ℂ) * QuditFidelity.depolarizingMap (d j) (hd j) 1 (M j) (y j) (y' j) +
        ((1 - p j : ℝ) : ℂ) * (M j) (y j) (y' j) := by
      intro j
      simp only [QuditFidelity.depolarizingMap, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast; ring
    simp only [hF, X6DE.key, depolarizingSubsetCoefficient]
    refine Finset.sum_congr rfl fun L _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> rfl
  rw [gen, Finset.mul_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  ring
