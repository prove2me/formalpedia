-- Prove2me | solution 1 for SeqLoss.TreeRules.edge_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:36:26.434083+00:00
-- url     : https://prove2.me/submissions/a45dad6a-f6ba-4916-a3c2-522d0db6d760

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

private lemma homogeneous (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
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




theorem solution (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
    (hφ : IsTreeRule φ) (hadd : TreeAdditive φ) (T : Finset (ℕ × ℕ)) (hT : IsTree T)
    (ℓ : ℕ × ℕ → ℝ) (hℓ : IsTreeLoss ℓ) :
    ∀ i ∈ N T, φ T ℓ i = ∑ e ∈ T, ℓ e * φ T (Pi.single e 1) i := by
  classical
  intro i hi
  have hz : φ T (0 : ℕ × ℕ → ℝ) i = 0 := by
    have hh := hadd T hT 0 0 (fun _ => le_rfl) (fun _ => le_rfl) i hi
    simp only [zero_add] at hh
    linarith
  let f : (ℕ × ℕ) → (ℕ × ℕ → ℝ) := fun e => ℓ e • Pi.single e 1
  have hf (e : ℕ × ℕ) : IsTreeLoss (f e) := by
    intro x
    dsimp [f]
    exact mul_nonneg (hℓ e) (by simp only [Pi.single_apply]; split_ifs <;> positivity)
  have hsum (S : Finset (ℕ × ℕ)) : IsTreeLoss (∑ e ∈ S, f e) := by
    intro x
    simpa only [Finset.sum_apply] using Finset.sum_nonneg (fun e _ => hf e x)
  have hfinite (S : Finset (ℕ × ℕ)) : φ T (∑ e ∈ S, f e) i = ∑ e ∈ S, φ T (f e) i := by
    induction S using Finset.induction_on with
    | empty => simpa using hz
    | @insert e S he ih =>
      simp only [Finset.sum_insert he]
      rw [← hadd T hT (f e) (∑ a ∈ S, f a) (hf e) (hsum S) i hi, ih]
  let b : ℕ × ℕ → ℝ := fun e => if e ∈ T then 0 else ℓ e
  have hb : IsTreeLoss b := by
    intro e
    dsimp [b]
    split_ifs
    · exact le_rfl
    · exact hℓ e
  have hbtotal : ∑ e ∈ T, b e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simp only [b, if_pos he]
  have hbzero : φ T b i = 0 := by
    have hnonneg := (hφ T hT b hb).1
    have hbound : φ T b i ≤ ∑ j ∈ N T, φ T b j :=
      Finset.single_le_sum (fun j hj => hnonneg j hj) hi
    have htotal := (hφ T hT b hb).2.1
    rw [htotal, hbtotal] at hbound
    exact le_antisymm hbound (hnonneg i hi)
  have hsplit : (∑ e ∈ T, f e) + b = ℓ := by
    funext x
    simp only [Finset.sum_apply, f, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Pi.add_apply]
    by_cases hx : x ∈ T
    · simp [b, hx, eq_comm]
    · simp [b, hx, eq_comm]
  have hadd' := hadd T hT (∑ e ∈ T, f e) b (hsum T) hb i hi
  rw [hsplit, hbzero, add_zero] at hadd'
  rw [← hadd', hfinite]
  apply Finset.sum_congr rfl
  intro e he
  exact homogeneous φ hφ hadd T hT (Pi.single e 1)
    (by intro x; simp only [Pi.single_apply]; split_ifs <;> positivity) (ℓ e) (hℓ e) i hi

#print axioms solution


