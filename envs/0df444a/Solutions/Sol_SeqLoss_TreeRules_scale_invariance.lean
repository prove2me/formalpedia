-- Prove2me | solution 1 for SeqLoss.TreeRules.scale_invariance
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:36:46.104435+00:00
-- url     : https://prove2.me/submissions/62b851cb-4fcd-457d-b848-88d8fd5aa8dd

import Definitions.Def_SeqLoss_TreeRules_Axioms
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open scoped NNReal
open SeqLoss.TreeRules

private lemma positive_additive_linear (f : ℝ≥0 →+ ℝ)
    (hf : ∀ a, 0 ≤ f a) (a : ℝ≥0) : f a = (a : ℝ) * f 1 := by
  have hmono : Monotone f := by
    intro x y hxy
    obtain ⟨c, rfl⟩ := exists_add_of_le hxy
    rw [map_add]
    exact le_add_of_nonneg_right (hf c)
  have hq (q : ℚ≥0) : f (q : ℝ≥0) = (q : ℝ) * f 1 := by
    simpa only [smul_eq_mul, mul_one] using map_nnratCast_smul f ℝ≥0 ℝ q 1
  rcases eq_or_lt_of_le (hf 1) with hzero | hpos
  · obtain ⟨n, hn⟩ := exists_nat_gt (a : ℝ)
    have han : a ≤ (n : ℝ≥0) := by exact_mod_cast hn.le
    have hh := hmono han
    have hnval : f (n : ℝ≥0) = (n : ℝ) * f 1 := by
      simpa using hq (n : ℚ≥0)
    rw [hnval, ← hzero, mul_zero] at hh
    rw [← hzero, mul_zero]
    exact le_antisymm hh (hf a)
  · apply le_antisymm
    · by_contra h
      have ha : (a : ℝ) < f a / f 1 := (lt_div_iff₀ hpos).mpr (lt_of_not_ge h)
      obtain ⟨q, haq, hqf⟩ := exists_rat_btwn ha
      have hq0 : 0 ≤ q := by exact_mod_cast (le_trans a.coe_nonneg haq.le)
      let q' : ℚ≥0 := ⟨q, hq0⟩
      have haq' : a ≤ (q' : ℝ≥0) := by exact_mod_cast haq.le
      have hh := hmono haq'
      rw [hq q'] at hh
      have hqf' : (q' : ℝ) * f 1 < f a :=
        (lt_div_iff₀ hpos).mp hqf
      linarith
    · by_contra h
      have ha : f a / f 1 < (a : ℝ) := (div_lt_iff₀ hpos).mpr (lt_of_not_ge h)
      obtain ⟨q, hfq, hqa⟩ := exists_rat_btwn ha
      have hq0 : 0 ≤ q := by
        exact_mod_cast (le_trans (div_nonneg (hf a) hpos.le) hfq.le)
      let q' : ℚ≥0 := ⟨q, hq0⟩
      have hqa' : (q' : ℝ≥0) ≤ a := by exact_mod_cast hqa.le
      have hh := hmono hqa'
      rw [hq q'] at hh
      have hfq' : f a < (q' : ℝ) * f 1 :=
        (div_lt_iff₀ hpos).mp hfq
      linarith

theorem solution (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
    (hφ : IsTreeRule φ) (hadd : TreeAdditive φ) (T : Finset (ℕ × ℕ)) (hT : IsTree T)
    (ℓ : ℕ × ℕ → ℝ) (hℓ : IsTreeLoss ℓ) (α : ℝ) (hα : 0 ≤ α) :
    ∀ i ∈ N T, φ T (α • ℓ) i = α * φ T ℓ i := by
  intro i hi
  have hscale (a : ℝ≥0) : IsTreeLoss ((a : ℝ) • ℓ) := by
    intro e
    exact mul_nonneg a.coe_nonneg (hℓ e)
  have hz : φ T (0 : ℕ × ℕ → ℝ) i = 0 := by
    have hh := hadd T hT 0 0 (fun _ => le_rfl) (fun _ => le_rfl) i hi
    simp only [zero_add] at hh
    linarith
  let f : ℝ≥0 →+ ℝ := {
    toFun := fun a => φ T ((a : ℝ) • ℓ) i
    map_zero' := by simpa using hz
    map_add' := by
      intro a b
      simp only [NNReal.coe_add, add_smul]
      exact (hadd T hT _ _ (hscale a) (hscale b) i hi).symm }
  have hnonneg (a : ℝ≥0) : 0 ≤ f a :=
    (hφ T hT _ (hscale a)).1 i hi
  have h := positive_additive_linear f hnonneg (⟨α,hα⟩ : ℝ≥0)
  change φ T (α • ℓ) i = α * φ T ((1 : ℝ) • ℓ) i at h
  simpa only [one_smul] using h

#print axioms solution


