-- Prove2me | solution 1 for SimchiLeviAddOn.Learning.lemma_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T10:51:28.69118+00:00
-- url     : https://prove2.me/submissions/c9e62474-25c8-41cc-9084-9091685bd38c

import Definitions.Def_SimchiLeviAddOn_Learning_Model

open scoped BigOperators ENNReal
open SimchiLeviAddOn.Learning

@[reducible] def witnessMarket : Market where
  N := 1
  M := 1
  nc := 1
  ns := 1
  na := 1
  S := 1
  hN := by decide
  hM := by decide
  hc := by decide
  hs := by decide
  ha := by decide
  core := fun _ => 1
  original := fun _ => 1
  discount := fun _ => 100
  core_nonneg := fun _ => by norm_num
  original_nonneg := fun _ => by norm_num
  discount_nonneg := fun _ => by norm_num
  core_injective := fun a b _ => Subsingleton.elim a b
  original_injective := fun a b _ => Subsingleton.elim a b
  discount_injective := fun a b _ => Subsingleton.elim a b

@[reducible] def witnessTables : Tables witnessMarket
  | .discounted _ _ => 1
  | _ => 0

@[reducible] def witnessPolicy : Policy witnessMarket where
  core := fun _ => 0
  original := fun _ => 0
  discount := fun _ => 0
  selected := fun _ => true

private lemma witnessPolicy_feasible : PrintedFeasible witnessMarket witnessPolicy := by
  refine ⟨?_, ?_⟩
  · decide
  · intro m
    norm_num [witnessMarket, witnessPolicy]

private lemma primarySupport_zero (p : Policy witnessMarket) :
    primarySupport witnessMarket witnessTables p = 0 := by
  simp [primarySupport, witnessMarket, witnessTables]

private lemma priceScale_witness : priceScale witnessMarket = 1 := by
  dsimp [priceScale]
  have hc : Set.range witnessMarket.core = {(1 : ℝ)} := by
    ext x
    simp [witnessMarket]
  rw [hc]
  simp

private lemma printedSupportiveValue_zero :
    printedSupportiveValue witnessMarket witnessTables 0 = 0 := by
  dsimp [printedSupportiveValue]
  have hset : {v : ℝ | ∃ p : Policy witnessMarket,
      PrintedFeasible witnessMarket p ∧
      v = primarySupport witnessMarket witnessTables p +
        0 * addonSupport witnessMarket witnessTables p} = {(0 : ℝ)} := by
    ext v
    simp only [Set.mem_ofPred, Set.mem_singleton_iff, zero_mul, add_zero]
    constructor
    · rintro ⟨p, _, rfl⟩
      exact primarySupport_zero p
    · rintro rfl
      exact ⟨witnessPolicy, witnessPolicy_feasible, (primarySupport_zero witnessPolicy).symm⟩
  rw [hset, csSup_singleton]

private lemma printedSupportiveValue_one_ge :
    100 ≤ printedSupportiveValue witnessMarket witnessTables 1 := by
  dsimp [printedSupportiveValue]
  refine le_csSup ?_ ?_
  · refine ⟨100, ?_⟩
    rintro v ⟨p, _, rfl⟩
    rw [primarySupport_zero p, zero_add, one_mul]
    change (∑ m : Fin 1, if p.selected m then
      witnessTables (.discounted m (p.discount m)) * witnessMarket.discount (p.discount m)
      else witnessTables (.ordinary m (p.original m)) * witnessMarket.original (p.original m)) ≤ 100
    rw [Fin.sum_univ_one]
    by_cases hsel : p.selected 0 <;> simp [hsel, witnessTables, witnessMarket]
  · refine ⟨witnessPolicy, witnessPolicy_feasible, ?_⟩
    rw [primarySupport_zero witnessPolicy, zero_add, one_mul]
    change (100 : ℝ) = ∑ m : Fin 1, if witnessPolicy.selected m then
      witnessTables (.discounted m (witnessPolicy.discount m)) * witnessMarket.discount (witnessPolicy.discount m)
      else witnessTables (.ordinary m (witnessPolicy.original m)) * witnessMarket.original (witnessPolicy.original m)
    rw [Fin.sum_univ_one]
    simp [witnessTables]

theorem solution :
    ¬ (∀ (X : Market) (d : Tables X) (_hd : IsDemand X d)
      (_hX : ∃ p : Policy X, PrintedFeasible X p),
      ∀ γ δ : ℝ, 0 ≤ γ → 0 ≤ δ →
        |printedSupportiveValue X d γ - printedSupportiveValue X d δ| ≤
          (X.M : ℝ) * priceScale X * |γ - δ|) := by
  intro h
  have hd : IsDemand witnessMarket witnessTables := by
    intro k
    cases k <;> simp [witnessTables]
  have hbound := h witnessMarket witnessTables hd ⟨witnessPolicy, witnessPolicy_feasible⟩ 1 0
    (by norm_num) (by norm_num)
  rw [printedSupportiveValue_zero, priceScale_witness] at hbound
  have h100 := printedSupportiveValue_one_ge
  have hM : (witnessMarket.M : ℝ) = 1 := by norm_num
  have habs : |(1 : ℝ) - 0| = 1 := by norm_num
  rw [hM, habs] at hbound
  have hle : printedSupportiveValue witnessMarket witnessTables 1 - 0 ≤
      |printedSupportiveValue witnessMarket witnessTables 1 - 0| := le_abs_self _
  linarith
