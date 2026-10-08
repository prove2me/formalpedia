-- Prove2me | solution 1 for UnitCircleRetainedIncidenceLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T19:31:06.825431+00:00
-- url     : https://prove2.me/submissions/86e8dada-c587-488f-b7fa-eb6ef995e5a3

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_UnitCircle
import Definitions.Def_unitDist
import Definitions.Def_UnitCircleIncidenceCount
import Theorems.Thm_UnitCircleIncidenceDoubleCount

open Classical
open scoped BigOperators
open scoped Real
noncomputable section

theorem solution
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    2 * (unitDist P : ℝ) - 2 * (P.card : ℝ) ≤
      ∑ p ∈ P.filter
          (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card),
        ((P.filter (fun q => q ∈ UnitCircle p)).card : ℝ) := by
  let r : EuclideanSpace ℝ (Fin 2) → ℕ :=
    fun p => (P.filter (fun q => q ∈ UnitCircle p)).card
  let good : EuclideanSpace ℝ (Fin 2) → Prop := fun p => 3 ≤ r p
  have hcount_sum_nat : UnitCircleIncidenceCount P = ∑ p ∈ P, r p := by
    let S : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
      (P.product P).filter (fun pq => pq.2 ∈ UnitCircle pq.1)
    have hmap : (S : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))).MapsTo
        Prod.fst P := by
      intro pq hpq
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hpq).1).1
    have hcard :
        S.card = ∑ p ∈ P, (S.filter (fun pq => pq.1 = p)).card := by
      simpa [Finset.sum_filter] using
        (Finset.card_eq_sum_card_fiberwise (s := S) (t := P) (f := Prod.fst) hmap)
    unfold UnitCircleIncidenceCount
    rw [hcard]
    refine Finset.sum_congr rfl ?_
    intro p hp
    apply Finset.card_bij
      (fun pq _hpq => pq.2)
    · intro pq hpq
      rcases Finset.mem_filter.mp hpq with ⟨hpqS, hpqfst⟩
      rcases Finset.mem_filter.mp hpqS with ⟨hpqprod, hpqcircle⟩
      rcases Finset.mem_product.mp hpqprod with ⟨_hp, hq⟩
      exact Finset.mem_filter.mpr ⟨hq, by simpa [hpqfst, r] using hpqcircle⟩
    · intro pq₁ hpq₁ pq₂ hpq₂ hsecond
      rcases Finset.mem_filter.mp hpq₁ with ⟨_hpq₁S, hpq₁fst⟩
      rcases Finset.mem_filter.mp hpq₂ with ⟨_hpq₂S, hpq₂fst⟩
      ext <;> simp [hpq₁fst, hpq₂fst, hsecond]
    · intro q hq
      refine ⟨(p, q), ?_, rfl⟩
      rcases Finset.mem_filter.mp hq with ⟨hqP, hqcircle⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hp, hqP⟩, by simpa using hqcircle⟩,
          rfl⟩
  have hdouble_nat : ∑ p ∈ P, r p = 2 * unitDist P := by
    simpa [hcount_sum_nat] using UnitCircleIncidenceDoubleCount P
  have hsplit_nat :
      ∑ p ∈ P, r p =
        (∑ p ∈ P.filter good, r p) + (∑ p ∈ P.filter (fun p => ¬ good p), r p) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := P) (p := good) (f := r)]
  have hbad_each :
      ∀ p ∈ P.filter (fun p => ¬ good p), r p ≤ 2 := by
    intro p hp
    have hpbad : ¬ good p := (Finset.mem_filter.mp hp).2
    dsimp [good] at hpbad
    omega
  have hbad_sum_nat :
      ∑ p ∈ P.filter (fun p => ¬ good p), r p ≤
        2 * (P.filter (fun p => ¬ good p)).card := by
    calc
      ∑ p ∈ P.filter (fun p => ¬ good p), r p
          ≤ ∑ p ∈ P.filter (fun p => ¬ good p), 2 := by
            exact Finset.sum_le_sum hbad_each
      _ = 2 * (P.filter (fun p => ¬ good p)).card := by
            simp [Finset.sum_const, Nat.mul_comm]
  have hbad_card : (P.filter (fun p => ¬ good p)).card ≤ P.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hbad_sum_nat' :
      ∑ p ∈ P.filter (fun p => ¬ good p), r p ≤ 2 * P.card := by
    exact hbad_sum_nat.trans (Nat.mul_le_mul_left 2 hbad_card)
  have hnat :
      2 * unitDist P ≤ (∑ p ∈ P.filter good, r p) + 2 * P.card := by
    calc
      2 * unitDist P = ∑ p ∈ P, r p := hdouble_nat.symm
      _ = (∑ p ∈ P.filter good, r p) + (∑ p ∈ P.filter (fun p => ¬ good p), r p) :=
            hsplit_nat
      _ ≤ (∑ p ∈ P.filter good, r p) + 2 * P.card :=
            Nat.add_le_add_left hbad_sum_nat' _
  have hreal :
      (2 * unitDist P : ℝ) ≤
        (∑ p ∈ P.filter good, (r p : ℝ)) + 2 * (P.card : ℝ) := by
    exact_mod_cast hnat
  dsimp [r, good] at hreal ⊢
  linarith
