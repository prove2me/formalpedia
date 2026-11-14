-- Prove2me | solution 1 for SaglamGV.card_circuits_le
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T11:25:50.66509+00:00
-- url     : https://prove2.me/submissions/d2028076-c747-4dff-a0fb-5d03b53e2feb

import Theorems.Thm_SaglamGV_circuit_sum_rank
import Definitions.Def_SaglamGV_Walk
set_option autoImplicit false
open Finset SaglamGV

private lemma tuple_count (n d ℓ : ℕ) :
    (circuits n d ℓ).card * ℓ.factorial ≤
      (Finset.univ.filter (fun t : Fin ℓ → (Fin n → ZMod 2) ↦
        (∀ i, t i ∈ ballP n d) ∧ ∑ i, t i = 0)).card := by
  classical
  let C := circuits n d ℓ
  let T := Finset.univ.filter (fun t : Fin ℓ → (Fin n → ZMod 2) ↦
    (∀ i, t i ∈ ballP n d) ∧ ∑ i, t i = 0)
  have hc (S : C) : S.val.card = ℓ := (Finset.mem_filter.mp S.property).2
  have hb (S : C) : S.val ⊆ ballP n d := by
    have h := (Finset.mem_filter.mp S.property).1
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp h).1
  let f : (Σ S : C, Fin ℓ ≃ S.val) → T := fun a ↦ by
    obtain ⟨S, e⟩ := a
    refine ⟨fun i ↦ (e i).val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · intro i
      exact hb S (e i).property
    · calc
        ∑ i, (e i).val = ∑ x : S.val, x.val := e.sum_comp _
        _ = ∑ x ∈ S.val, x := Finset.sum_coe_sort S.val (fun x : Fin n → ZMod 2 ↦ x)
        _ = 0 := (SaglamGV.circuit_sum_rank n d ℓ S.val S.property).1
  have hrange (S : C) (e : Fin ℓ ≃ S.val) :
      Set.range (fun i ↦ (e i).val) = (S.val : Set (Fin n → ZMod 2)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hf : Function.Injective f := by
    rintro ⟨S, e⟩ ⟨S', e'⟩ h
    have ht : (fun i ↦ (e i).val) = (fun i ↦ (e' i).val) := congrArg Subtype.val h
    have hSS : S = S' := by
      apply Subtype.ext
      apply Finset.coe_injective
      rw [← hrange S e, ← hrange S' e', ht]
    cases hSS
    have he : e = e' := by
      apply Equiv.ext
      intro i
      apply Subtype.ext
      exact congrFun ht i
    cases he
    rfl
  have hecard (S : C) : Fintype.card (Fin ℓ ≃ S.val) = ℓ.factorial := by
    let e : Fin ℓ ≃ S.val := Fintype.equivOfCardEq (by simp [hc S])
    simpa using Fintype.card_equiv e
  have hcount := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_sigma, hecard, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, smul_eq_mul, C, T] using hcount

theorem solution (n d ℓ : ℕ) :
    ((circuits n d ℓ).card : ℝ) ≤
      (vol n d : ℝ) ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ := by
  classical
  by_cases hV : vol n d = 0
  · have hball : ballP n d = ∅ := Finset.card_eq_zero.mp hV
    have hc : circuits n d ℓ = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      have hsub : S ⊆ ballP n d := by
        exact Finset.mem_powerset.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
      have he : S = ∅ := Finset.subset_empty.mp (hball ▸ hsub)
      have hcard := (Finset.mem_filter.mp hS).2
      have hthree := (SaglamGV.circuit_sum_rank n d ℓ S hS).2.2.1
      simp only [he, Finset.card_empty] at hcard
      omega
    rw [hc]
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold zeroSumProb
    positivity
  · have hcount : ((circuits n d ℓ).card : ℝ) * (ℓ.factorial : ℝ) ≤
        ((Finset.univ.filter (fun t : Fin ℓ → (Fin n → ZMod 2) ↦
          (∀ i, t i ∈ ballP n d) ∧ ∑ i, t i = 0)).card : ℝ) := by
      exact_mod_cast tuple_count n d ℓ
    have hfact : (0 : ℝ) < ℓ.factorial := Nat.cast_pos.mpr (Nat.factorial_pos ℓ)
    have hpow : (vol n d : ℝ) ^ ℓ ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hV)
    unfold zeroSumProb
    calc
      _ ≤ _ / (ℓ.factorial : ℝ) := (le_div_iff₀ hfact).mpr hcount
      _ = _ := by field_simp
