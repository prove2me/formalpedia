-- Prove2me | solution 1 for SteinitzExchange.Extension.conjugate_closure_perturb
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:51:11.604188+00:00
-- url     : https://prove2.me/submissions/b0b5a58e-6f1a-40cd-b30f-fe386ac07e51

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

theorem aux_ccp_pairing_sub {V : Type*} [Fintype V] (p q b : V → ℝ) :
    pairing (p - q) b = pairing p b - pairing q b := by
  unfold pairing
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem aux_ccp_pairing_add {V : Type*} [Fintype V] (p q b : V → ℝ) :
    pairing (p + q) b = pairing p b + pairing q b := by
  unfold pairing
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.add_apply]
  ring

theorem aux_ccp_isLinear {V : Type*} [Fintype V] (q : V → ℝ) :
    IsLinearMap ℝ (fun b : V → ℝ => pairing q b) := by
  constructor
  · intro x y
    unfold pairing
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Pi.add_apply]
    ring
  · intro c x
    unfold pairing
    rw [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem aux_ccp_conj_le {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (g : (V → ℤ) → ℝ) (q : V → ℝ) (x : V → ℤ) (hx : x ∈ B) :
    concaveConj B g q ≤ pairing q (toReal x) - g x := by
  unfold concaveConj
  have hbdd : BddBelow (Set.range fun y : (B : Set (V → ℤ)) =>
      (pairing q (toReal (y : V → ℤ)) - g y)) :=
    (Set.finite_range _).bddBelow
  exact ciInf_le hbdd (⟨x, by simpa using hx⟩ : (B : Set (V → ℤ)))

theorem aux_ccp_bdd {V : Type*} [Fintype V] (B : Finset (V → ℤ)) (hB : B.Nonempty)
    (g : (V → ℤ) → ℝ) (b : V → ℝ) (hb : b ∈ hull B) :
    BddBelow (Set.range fun q : V → ℝ => pairing q b - concaveConj B g q) := by
  obtain ⟨x₀, _, hx₀⟩ := Finset.exists_min_image B g hB
  refine ⟨g x₀, ?_⟩
  rintro _ ⟨q, rfl⟩
  have hsub : toReal '' (B : Set (V → ℤ)) ⊆
      {w | g x₀ + concaveConj B g q ≤ (fun b : V → ℝ => pairing q b) w} := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := aux_ccp_conj_le B g q x (by simpa using hx)
    have h2 := hx₀ x (by simpa using hx)
    simp only [Set.mem_ofPred_eq]
    linarith
  have hconv := convex_halfSpace_ge (aux_ccp_isLinear q) (g x₀ + concaveConj B g q)
  have := convexHull_min hsub hconv hb
  simp only [Set.mem_ofPred_eq] at this
  show g x₀ ≤ pairing q b - concaveConj B g q
  linarith

end SteinitzExchange.Extension

open SteinitzExchange.Extension

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (p₀ : V → ℝ) :
    (∀ p : V → ℝ, concaveConj B (perturb g p₀) p = concaveConj B g (p - p₀)) ∧
    (∀ b ∈ hull B, concaveClosure B (perturb g p₀) b = concaveClosure B g b + pairing p₀ b) := by
  have h1 : ∀ p : V → ℝ, concaveConj B (perturb g p₀) p = concaveConj B g (p - p₀) := by
    intro p
    unfold concaveConj perturb
    refine iInf_congr fun x => ?_
    rw [aux_ccp_pairing_sub]
    ring
  refine ⟨h1, ?_⟩
  intro b hb
  unfold concaveClosure
  simp_rw [h1]
  rw [ciInf_add (aux_ccp_bdd B hB g b hb)]
  rw [← (Equiv.addRight p₀).surjective.iInf_comp]
  refine iInf_congr fun q => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, aux_ccp_pairing_add]
  ring
