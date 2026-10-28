-- Prove2me | solution 1 for TokenComplexity.Tradeoff.eqs_11_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T01:33:29.415655+00:00
-- url     : https://prove2.me/submissions/a6214de1-9daf-45f3-8bd6-0ef1e1d81b94

import Mathlib
import Definitions.Def_TokenComplexity_Tradeoff_Model

namespace Aux_TC_1112

open Finset

lemma mapA {n : ℕ} (τ : Fin n → ℕ∞) (t : Fin n → ℕ) :
    ∃ x : Fin n → Bool, (∀ i, x i = true → τ i ≠ ⊤) ∧
      ((univ.filter (fun i => x i = true)).card : ℝ) =
        ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) ∧
      (∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ)) ≤ ∑ i, (t i : ℝ) := by
  refine ⟨fun i => decide (τ i ≤ (t i : ℕ∞)), fun i hi => ?_, ?_, ?_⟩
  · simp only [decide_eq_true_eq] at hi
    exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hi
  · congr 2
    ext i; simp
  · have hf : univ.filter (fun i => decide (τ i ≤ (t i : ℕ∞)) = true) =
        univ.filter (fun i => τ i ≤ (t i : ℕ∞)) := by ext i; simp
    rw [hf]
    calc ∑ i ∈ univ.filter (fun i => τ i ≤ (t i : ℕ∞)), ((τ i).toNat : ℝ)
        ≤ ∑ i ∈ univ.filter (fun i => τ i ≤ (t i : ℕ∞)), (t i : ℝ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          simp only [mem_filter, mem_univ, true_and] at hi
          have := ENat.toNat_le_toNat hi (ENat.coe_ne_top _)
          rw [ENat.toNat_coe] at this
          exact_mod_cast this
      _ ≤ ∑ i, (t i : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun i _ _ => Nat.cast_nonneg _)

lemma mapB {n : ℕ} (τ : Fin n → ℕ∞) (x : Fin n → Bool) (hx : ∀ i, x i = true → τ i ≠ ⊤) :
    ∃ t : Fin n → ℕ, (∑ i, (t i : ℝ)) =
        ∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ) ∧
      ((univ.filter (fun i => x i = true)).card : ℝ) ≤
        ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) := by
  refine ⟨fun i => if x i = true then (τ i).toNat else 0, ?_, ?_⟩
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Nat.cast_ite, Nat.cast_zero]
  · have : univ.filter (fun i => x i = true) ⊆
        univ.filter (fun i => τ i ≤ ((if x i = true then (τ i).toNat else 0 : ℕ) : ℕ∞)) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      rw [if_pos hi, ENat.coe_toNat (hx i hi)]
    exact_mod_cast Finset.card_le_card this

end Aux_TC_1112

open Finset Aux_TC_1112 in
theorem solution {n : ℕ} (τ : Fin n → ℕ∞) :
    (∀ T v : ℝ,
      IsGreatest {a | ∃ t : Fin n → ℕ, (∑ i, (t i : ℝ)) / n ≤ T ∧
        a = ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n} v ↔
      IsGreatest {a | ∃ x : Fin n → Bool, (∀ i, x i = true → τ i ≠ ⊤) ∧
        (∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ)) / n ≤ T ∧
        a = ((univ.filter (fun i => x i = true)).card : ℝ) / n} v) ∧
    (∀ α v : ℝ,
      IsLeast {L | ∃ t : Fin n → ℕ,
        α ≤ ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n ∧
        L = (∑ i, (t i : ℝ)) / n} v ↔
      IsLeast {L | ∃ x : Fin n → Bool, (∀ i, x i = true → τ i ≠ ⊤) ∧
        α ≤ ((univ.filter (fun i => x i = true)).card : ℝ) / n ∧
        L = (∑ i ∈ univ.filter (fun i => x i = true), ((τ i).toNat : ℝ)) / n} v) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨fun T v => ⟨?_, ?_⟩, fun α v => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨t, ht, rfl⟩, hmax⟩
    obtain ⟨x, hx, hacc, hcost⟩ := mapA τ t
    refine ⟨⟨x, hx, le_trans (div_le_div_of_nonneg_right hcost hn) ht, by rw [hacc]⟩, ?_⟩
    rintro a ⟨x', hx', hc', rfl⟩
    obtain ⟨t', hct, hat⟩ := mapB τ x' hx'
    refine le_trans (div_le_div_of_nonneg_right hat hn) (hmax ⟨t', ?_, rfl⟩)
    rw [hct]; exact hc'
  · rintro ⟨⟨x, hx, hc, rfl⟩, hmax⟩
    obtain ⟨t, hct, hat⟩ := mapB τ x hx
    have ht : (∑ i, (t i : ℝ)) / n ≤ T := by rw [hct]; exact hc
    obtain ⟨x', hx', hacc', hcost'⟩ := mapA τ t
    have hle : ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n ≤
        ((univ.filter (fun i => x i = true)).card : ℝ) / n := by
      refine hmax ⟨x', hx', le_trans (div_le_div_of_nonneg_right hcost' hn) ht, ?_⟩
      rw [hacc']
    have heq : ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n =
        ((univ.filter (fun i => x i = true)).card : ℝ) / n :=
      le_antisymm hle (div_le_div_of_nonneg_right hat hn)
    refine ⟨⟨t, ht, heq.symm⟩, ?_⟩
    rintro a ⟨t'', ht'', rfl⟩
    obtain ⟨x'', hx'', hacc'', hcost''⟩ := mapA τ t''
    refine hmax ⟨x'', hx'', le_trans (div_le_div_of_nonneg_right hcost'' hn) ht'', ?_⟩
    rw [hacc'']
  · rintro ⟨⟨t, ht, rfl⟩, hmin⟩
    obtain ⟨x, hx, hacc, hcost⟩ := mapA τ t
    have hxa : α ≤ ((univ.filter (fun i => x i = true)).card : ℝ) / n := by rw [hacc]; exact ht
    obtain ⟨t', hct, hat⟩ := mapB τ x hx
    have h1 : (∑ i, (t i : ℝ)) / n ≤ (∑ i ∈ univ.filter (fun i => x i = true),
        ((τ i).toNat : ℝ)) / n := by
      refine hmin ⟨t', le_trans hxa (div_le_div_of_nonneg_right hat hn), ?_⟩
      rw [hct]
    have heq := le_antisymm (div_le_div_of_nonneg_right hcost hn) h1
    refine ⟨⟨x, hx, hxa, heq.symm⟩, ?_⟩
    rintro L ⟨x', hx', ha', rfl⟩
    obtain ⟨t'', hct'', hat''⟩ := mapB τ x' hx'
    refine hmin ⟨t'', le_trans ha' (div_le_div_of_nonneg_right hat'' hn), ?_⟩
    rw [hct'']
  · rintro ⟨⟨x, hx, ha, rfl⟩, hmin⟩
    obtain ⟨t, hct, hat⟩ := mapB τ x hx
    refine ⟨⟨t, le_trans ha (div_le_div_of_nonneg_right hat hn), by rw [hct]⟩, ?_⟩
    rintro L ⟨t', ht', rfl⟩
    obtain ⟨x', hx', hacc', hcost'⟩ := mapA τ t'
    refine le_trans (hmin ⟨x', hx', by rw [hacc']; exact ht', rfl⟩)
      (div_le_div_of_nonneg_right hcost' hn)
