-- Prove2me | solution 1 for SteinitzExchange.Extension.concaveClosure_concaveOn
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:03:46.155275+00:00
-- url     : https://prove2.me/submissions/e15cbefd-899d-434d-8802-555531ed4e18

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

theorem aux_cc_pairing_comb {V : Type*} [Fintype V] (p x y : V → ℝ) (a b : ℝ) :
    pairing p (a • x + b • y) = a * pairing p x + b * pairing p y := by
  unfold pairing
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem aux_cc_conj_le {V : Type*} [Fintype V] (B : Finset (V → ℤ)) (g : (V → ℤ) → ℝ)
    (p : V → ℝ) (z : V → ℤ) (hz : z ∈ B) :
    concaveConj B g p ≤ pairing p (toReal z) - g z := by
  unfold concaveConj
  have hbdd : BddBelow (Set.range fun x : (B : Set (V → ℤ)) =>
      pairing p (toReal (x : V → ℤ)) - g x) :=
    (Set.finite_range _).bddBelow
  exact ciInf_le hbdd (⟨z, hz⟩ : (B : Set (V → ℤ)))

theorem aux_cc_lower {V : Type*} [Fintype V] (B : Finset (V → ℤ)) (hB : B.Nonempty)
    (g : (V → ℤ) → ℝ) (p : V → ℝ) (x : V → ℝ) (hx : x ∈ hull B) :
    B.inf' hB g ≤ pairing p x - concaveConj B g p := by
  have hconv : Convex ℝ {x : V → ℝ | B.inf' hB g ≤ pairing p x - concaveConj B g p} := by
    intro u hu w hw a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hu hw ⊢
    rw [aux_cc_pairing_comb]
    obtain rfl : b = 1 - a := by linarith
    nlinarith [mul_nonneg ha (sub_nonneg.2 hu), mul_nonneg hb (sub_nonneg.2 hw)]
  have hsub : toReal '' (B : Set (V → ℤ)) ⊆
      {x : V → ℝ | B.inf' hB g ≤ pairing p x - concaveConj B g p} := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_ofPred_eq]
    have h1 := aux_cc_conj_le B g p z hz
    have h2 : B.inf' hB g ≤ g z := Finset.inf'_le g hz
    linarith
  exact convexHull_min hsub hconv hx

end SteinitzExchange.Extension

open SteinitzExchange.Extension

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) :
    ConcaveOn ℝ (hull B) (concaveClosure B g) := by
  refine ⟨convex_convexHull ℝ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hbx : BddBelow (Set.range fun p : V → ℝ => pairing p x - concaveConj B g p) :=
    ⟨B.inf' hB g, by rintro _ ⟨p, rfl⟩; exact aux_cc_lower B hB g p x hx⟩
  have hby : BddBelow (Set.range fun p : V → ℝ => pairing p y - concaveConj B g p) :=
    ⟨B.inf' hB g, by rintro _ ⟨p, rfl⟩; exact aux_cc_lower B hB g p y hy⟩
  simp only [smul_eq_mul]
  unfold concaveClosure
  apply le_ciInf
  intro p
  rw [aux_cc_pairing_comb]
  have h1 := ciInf_le hbx p
  have h2 := ciInf_le hby p
  obtain rfl : b = 1 - a := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
