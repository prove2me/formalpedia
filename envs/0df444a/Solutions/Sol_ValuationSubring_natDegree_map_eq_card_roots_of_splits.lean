-- Prove2me | solution 1 for ValuationSubring.natDegree_map_eq_card_roots_of_splits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e5599d3b-da7d-5627-86ae-749164f030a7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_natDegree_map_eq_card_roots_of_splits

open scoped Polynomial
open Polynomial

namespace ValuationRingRootCount

variable {E k : Type*} [Field E] [Field k] (A : ValuationSubring E) (σ : A →+* k)
  (hσ : RingHom.ker σ = IsLocalRing.maximalIdeal A)

theorem algebraMap_injective : Function.Injective (algebraMap A E) := Subtype.val_injective

theorem isUnit_iff_inv_mem (z : A) (hz : (z : E) ≠ 0) : IsUnit z ↔ (z : E)⁻¹ ∈ A := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 := congrArg (fun w : A => (w : E)) u.mul_inv
    simp only [Subring.coe_one, hu] at h1
    push_cast at h1
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact SetLike.coe_mem _
  · intro h
    exact ⟨⟨z, ⟨(z : E)⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ hz), Subtype.ext (inv_mul_cancel₀ hz)⟩,
      rfl⟩

theorem inv_mem_maximalIdeal {α : E} (hα : α ∉ A) :
    ∃ h : α⁻¹ ∈ A, (⟨α⁻¹, h⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  have hα0 : α ≠ 0 := fun h => hα (h ▸ A.zero_mem)
  have hβA : α⁻¹ ∈ A := (A.mem_or_inv_mem α).resolve_left hα
  refine ⟨hβA, (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu => hα ?_)⟩
  have := (isUnit_iff_inv_mem A ⟨α⁻¹, hβA⟩ (inv_ne_zero hα0)).mp hu
  simpa using this

theorem coeff_mem_of_one_sub_mul (β : E) (hβ : β ∈ A) (q : E[X])
    (h : ∀ n, ((1 - C β * X) * q).coeff n ∈ A) (n : ℕ) : q.coeff n ∈ A := by
  induction n with
  | zero =>
    have := h 0
    rwa [sub_mul, one_mul, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul_zero, mul_zero,
      sub_zero] at this
  | succ n ih =>
    have := h (n + 1)
    rw [sub_mul, one_mul, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul] at this
    have e : q.coeff (n + 1) = (q.coeff (n + 1) - β * q.coeff n) + β * q.coeff n := by ring
    rw [e]
    exact A.add_mem _ _ this (A.mul_mem _ _ hβ ih)

include hσ in

theorem main (n : ℕ) : ∀ p : A[X], p.natDegree = n → p.map σ ≠ 0 →
    Multiset.card (p.map (algebraMap A E)).roots = p.natDegree →
    (p.map σ).natDegree = Multiset.card p.roots := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn hp hsplit
  have hp0 : p ≠ 0 := fun h => hp (by rw [h, Polynomial.map_zero])
  have hinj := algebraMap_injective A
  have hpE0 : p.map (algebraMap A E) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hp0
  by_cases h0 : p.natDegree = 0
  · obtain ⟨a, ha⟩ : ∃ a, p = C a := ⟨_, eq_C_of_natDegree_eq_zero h0⟩
    rw [ha, map_C, natDegree_C, roots_C, Multiset.card_zero]

  have hcard : 0 < Multiset.card (p.map (algebraMap A E)).roots := by
    rw [hsplit]; exact Nat.pos_of_ne_zero h0
  obtain ⟨α, hα⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
  have hroot : (p.map (algebraMap A E)).IsRoot α := (mem_roots hpE0).mp hα
  by_cases hαA : α ∈ A
  ·
    set a : A := ⟨α, hαA⟩ with ha_def
    have ha : p.IsRoot a := by
      apply hinj
      have : (p.map (algebraMap A E)).eval (algebraMap A E a) = 0 := hroot
      rw [map_zero]; rwa [eval_map, eval₂_at_apply] at this
    have hfac : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    set p₁ := p /ₘ (X - C a) with hp₁_def
    have hp₁0 : p₁ ≠ 0 := fun h => hp0 (by rw [← hfac, h, mul_zero])
    have hdeg : p.natDegree = p₁.natDegree + 1 := by
      rw [← hfac, natDegree_mul (X_sub_C_ne_zero a) hp₁0, natDegree_X_sub_C, add_comm]
    have hmapσ : p.map σ = (X - C (σ a)) * p₁.map σ := by
      rw [← hfac, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]
    have hp₁σ : p₁.map σ ≠ 0 := fun h => hp (by rw [hmapσ, h, mul_zero])
    have hdegσ : (p.map σ).natDegree = (p₁.map σ).natDegree + 1 := by
      rw [hmapσ, natDegree_mul (X_sub_C_ne_zero _) hp₁σ, natDegree_X_sub_C, add_comm]
    have hroots : p.roots = a ::ₘ p₁.roots := by
      rw [← hfac, roots_mul (hfac.symm ▸ hp0), roots_X_sub_C, Multiset.singleton_add]
    have hmapE : p.map (algebraMap A E) = (X - C α) * p₁.map (algebraMap A E) := by
      rw [← hfac, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]
      rfl
    have hp₁E0 : p₁.map (algebraMap A E) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hp₁0
    have hsplit₁ : Multiset.card (p₁.map (algebraMap A E)).roots = p₁.natDegree := by
      have := hsplit
      rw [hmapE, roots_mul (hmapE ▸ hpE0), roots_X_sub_C, Multiset.card_add,
        Multiset.card_singleton, hdeg] at this
      omega
    have := ih p₁.natDegree (by omega) p₁ rfl hp₁σ hsplit₁
    rw [hdegσ, hroots, Multiset.card_cons, this]
  ·
    obtain ⟨hβA, hβmax⟩ := inv_mem_maximalIdeal A hαA
    have hα0 : α ≠ 0 := fun h => hαA (h ▸ A.zero_mem)
    set β : A := ⟨α⁻¹, hβA⟩ with hβ_def
    have hσβ : σ β = 0 := by rw [← RingHom.mem_ker, hσ]; exact hβmax

    set qE : E[X] := C (-α) * (p.map (algebraMap A E) /ₘ (X - C α)) with hqE_def
    have hfacE : (1 - C (α⁻¹) * X) * qE = p.map (algebraMap A E) := by
      have h1 : (1 - C (α⁻¹) * X : E[X]) * C (-α) = X - C α := by
        have h2 : C (α⁻¹) * C (-α) = (-1 : E[X]) := by
          rw [← C_mul, mul_neg, inv_mul_cancel₀ hα0, map_neg, C_1]
        calc (1 - C (α⁻¹) * X : E[X]) * C (-α) = C (-α) - (C α⁻¹ * C (-α)) * X := by ring
          _ = X - C α := by rw [h2, map_neg]; ring
      rw [hqE_def, ← mul_assoc, h1]
      exact mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hqcoeff : ∀ m, qE.coeff m ∈ A := coeff_mem_of_one_sub_mul A α⁻¹ hβA qE (fun m => by
      rw [hfacE, coeff_map]; exact SetLike.coe_mem _)
    obtain ⟨q, hq⟩ : ∃ q : A[X], q.map (algebraMap A E) = qE := by
      rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
      exact fun m => ⟨⟨_, hqcoeff m⟩, rfl⟩
    have hfac : (1 - C β * X) * q = p := by
      apply Polynomial.map_injective _ hinj
      rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C,
        map_X, hq, ← hfacE]
      rfl
    have hq0 : q ≠ 0 := fun h => hp0 (by rw [← hfac, h, mul_zero])
    have hlin : (1 - C β * X : A[X]) = C (-β) * X + C 1 := by rw [map_neg, C_1]; ring
    have hβ0 : β ≠ 0 := fun h => by
      have := congrArg (fun z : A => (z : E)) h
      simp only [hβ_def, ZeroMemClass.coe_zero, inv_eq_zero] at this
      exact hα0 this
    have hlin0 : (1 - C β * X : A[X]) ≠ 0 := fun h => by
      have := congrArg natDegree h
      rw [hlin, natDegree_linear (neg_ne_zero.mpr hβ0), natDegree_zero] at this
      exact one_ne_zero this
    have hdeg : p.natDegree = q.natDegree + 1 := by
      rw [← hfac, natDegree_mul hlin0 hq0, hlin, natDegree_linear (neg_ne_zero.mpr hβ0), add_comm]
    have hmapσ : p.map σ = q.map σ := by
      rw [← hfac, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
        map_C, map_X, hσβ, C_0, zero_mul, sub_zero, one_mul]
    have hqσ : q.map σ ≠ 0 := hmapσ ▸ hp
    have hroots : p.roots = q.roots := by
      rw [← hfac, roots_mul (hfac.symm ▸ hp0)]
      have : (1 - C β * X : A[X]).roots = 0 := by
        refine Multiset.eq_zero_of_forall_notMem fun c hc => ?_
        have hc' := ((mem_roots hlin0).mp hc)
        have he : (1 - C β * X : A[X]).eval c = 1 - β * c := by
          simp [eval_sub, eval_one, eval_mul, eval_C, eval_X]
        rw [IsRoot.def, he, sub_eq_zero] at hc'
        have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
          rw [hc']; exact Ideal.mul_mem_right _ _ hβmax
        exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
          ((Ideal.eq_top_iff_one _).mpr h1)
      rw [this, zero_add]
    have hqE0 : qE ≠ 0 := by rw [← hq]; exact (Polynomial.map_ne_zero_iff hinj).mpr hq0
    have hsplit₁ : Multiset.card (q.map (algebraMap A E)).roots = q.natDegree := by
      have := hsplit
      have hlinE : (1 - C α⁻¹ * X : E[X]) = C (-α⁻¹) * (X - C α) := by
        have h2 : C (α⁻¹) * C α = (1 : E[X]) := by rw [← C_mul, inv_mul_cancel₀ hα0, C_1]
        calc (1 - C α⁻¹ * X : E[X]) = C α⁻¹ * C α - C α⁻¹ * X := by rw [h2]
          _ = C (-α⁻¹) * (X - C α) := by rw [map_neg]; ring
      rw [← hfacE, roots_mul (hfacE.symm ▸ hpE0), hlinE, roots_C_mul _ (neg_ne_zero.mpr
        (inv_ne_zero hα0)), roots_X_sub_C, Multiset.card_add, Multiset.card_singleton, hdeg]
        at this
      rw [hq]; omega
    have := ih q.natDegree (by omega) q rfl hqσ hsplit₁
    rw [hmapσ, hroots, this]

end ValuationRingRootCount

theorem solution
    {E k : Type*} [Field E] [Field k] (A : ValuationSubring E) (σ : A →+* k)
    (hσ : RingHom.ker σ = IsLocalRing.maximalIdeal A)
    (p : A[X]) (hp : p.map σ ≠ 0)
    (hsplit : Multiset.card (p.map (algebraMap A E)).roots = p.natDegree) :
    (p.map σ).natDegree = Multiset.card p.roots :=
  ValuationRingRootCount.main A σ hσ p.natDegree p rfl hp hsplit

end S_ValuationSubring_natDegree_map_eq_card_roots_of_splits
end P2MW
export P2MW.S_ValuationSubring_natDegree_map_eq_card_roots_of_splits (solution)
