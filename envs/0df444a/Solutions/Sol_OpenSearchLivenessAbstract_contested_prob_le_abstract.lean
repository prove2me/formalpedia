-- Prove2me | solution 1 for OpenSearchLivenessAbstract.contested_prob_le_abstract
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T18:53:08.827471+00:00
-- url     : https://prove2.me/submissions/3654ec30-cbc1-476f-9576-b44ce2ab7c2c

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic
import Definitions.Def_OpenSearchLivenessAbstract
open OpenSearchLivenessAbstract

private theorem sum_piSplitAt {ι A M : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    [AddCommMonoid M] (j : ι) (F : (ι → A) → M) :
    ∑ x, F x = ∑ r : {k // k ≠ j} → A, ∑ y : A, F ((Equiv.piSplitAt j (fun _ => A)).symm (y, r)) := by
  rw [← (Equiv.piSplitAt j (fun _ => A)).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]

private theorem piSplitAt_symm_self {ι A : Type*} [DecidableEq ι] (j : ι) (y : A)
    (r : {k // k ≠ j} → A) : (Equiv.piSplitAt j (fun _ => A)).symm (y, r) j = y := by
  simp [Equiv.piSplitAt_symm_apply]

private theorem piSplitAt_symm_ne {ι A : Type*} [DecidableEq ι] (j : ι) (y : A)
    (r : {k // k ≠ j} → A) (k : ι) (hk : k ≠ j) : (Equiv.piSplitAt j (fun _ => A)).symm (y, r) k = r ⟨k, hk⟩ := by
  simp [Equiv.piSplitAt_symm_apply, hk]

/-- For a fixed target `t`, at most `(2δ - 1) * K` draws give a delay less
than `δ` away from `t`: the open interval holds `2δ - 1` integers, each
with at most `K` preimages. -/
private theorem card_close_le_abstract (δ K : Nat) (hδ : 1 ≤ δ)
    (delay : Fin (2 ^ 64) → Int)
    (hpre : ∀ t : Int, (Finset.univ.filter (fun y => delay y = t)).card ≤ K)
    (t : Int) :
    (Finset.univ.filter (fun y => |t - delay y| < δ)).card ≤ (2 * δ - 1) * K := by
  have hsub : Finset.univ.filter (fun y => |t - delay y| < δ) ⊆
      (Finset.Icc (t - δ + 1) (t + δ - 1)).biUnion
        (fun d => Finset.univ.filter (fun y => delay y = d)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ, true_and]
    -- omega does not split the absolute value in `hy` here, so unwrap it
    -- explicitly with `abs_lt` before doing linear arithmetic.
    have habs : -(δ : Int) < t - delay y ∧ t - delay y < (δ : Int) := abs_lt.mp hy
    refine ⟨delay y, ⟨by omega, by omega⟩, rfl⟩
  calc (Finset.univ.filter (fun y => |t - delay y| < δ)).card
      ≤ ((Finset.Icc (t - δ + 1) (t + δ - 1)).biUnion
          (fun d => Finset.univ.filter (fun y => delay y = d))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ d ∈ Finset.Icc (t - δ + 1) (t + δ - 1),
          (Finset.univ.filter (fun y => delay y = d)).card := Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ Finset.Icc (t - δ + 1) (t + δ - 1), K :=
        Finset.sum_le_sum (fun d _ => hpre d)
    _ = (2 * δ - 1) * K := by
        rw [Finset.sum_const, Int.card_Icc, smul_eq_mul]
        have : (t + δ - 1 + 1 - (t - δ + 1)).toNat = 2 * δ - 1 := by omega
        rw [this]

/-- For two distinct candidates, few full draws make them fire less than `δ`
apart. -/
private theorem card_pair_close_le_abstract (n δ K : Nat) (hδ : 1 ≤ δ)
    (offset : Fin n → Int) (delay : Fin n → Fin (2 ^ 64) → Int)
    (hpre : ∀ j t, (Finset.univ.filter (fun y => delay j y = t)).card ≤ K)
    (i j : Fin n) (hij : i ≠ j) :
    (Finset.univ.filter (fun x : Fin n → Fin (2 ^ 64) =>
        |fireTime offset delay x i - fireTime offset delay x j| < δ)).card ≤
      (2 ^ 64) ^ (n - 1) * ((2 * δ - 1) * K) := by
  rw [Finset.card_filter, sum_piSplitAt j]
  calc ∑ r : {k // k ≠ j} → Fin (2 ^ 64), ∑ y : Fin (2 ^ 64),
        (if |fireTime offset delay ((Equiv.piSplitAt j (fun _ => Fin (2 ^ 64))).symm (y, r)) i -
            fireTime offset delay ((Equiv.piSplitAt j (fun _ => Fin (2 ^ 64))).symm (y, r)) j| < δ
          then 1 else 0)
      = ∑ r : {k // k ≠ j} → Fin (2 ^ 64), (Finset.univ.filter (fun y : Fin (2 ^ 64) =>
          |(offset i + delay i (r ⟨i, hij⟩) - offset j) -
            (delay j y : Int)| < δ)).card := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro y _
        unfold fireTime
        rw [piSplitAt_symm_self, piSplitAt_symm_ne _ _ _ _ hij]
        have : offset i + delay i (r ⟨i, hij⟩) -
            (offset j + delay j y) =
            (offset i + delay i (r ⟨i, hij⟩) - offset j) -
              (delay j y : Int) := by ring
        rw [this]
    _ ≤ ∑ _r : {k // k ≠ j} → Fin (2 ^ 64), (2 * δ - 1) * K :=
        Finset.sum_le_sum (fun r _ => card_close_le_abstract δ K hδ (delay j) (hpre j) _)
    _ = (2 ^ 64) ^ (n - 1) * ((2 * δ - 1) * K) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        congr 1
        simp

private theorem card_pairs_lt (n : ℕ) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 < ij.2)).card = n.choose 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ j : Fin n, (∑ i : Fin n, if (i, j).1 < (i, j).2 then 1 else 0) = j.val := by
    intro j
    rw [← Finset.card_filter, ← Fin.card_Iio j]
    congr 1
    ext i
    simp
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun m => m) n, Nat.choose_two_right, ← Finset.sum_range_id_mul_two,
    Nat.mul_div_cancel _ (by norm_num)]

theorem solution (n δ K : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (offset : Fin n → Int) (delay : Fin n → Fin (2 ^ 64) → Int)
    (hpre : ∀ j t, (Finset.univ.filter (fun y => delay j y = t)).card ≤ K) :
    ((Finset.univ.filter (fun x => ¬ Uncontested offset delay δ x)).card : ℚ) / (2 ^ 64) ^ n ≤
      (n.choose 2 : ℚ) * (2 * δ - 1 : ℕ) * K / 2 ^ 64 := by
  set P := (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 < ij.2) with hPdef
  set E : Fin n × Fin n → Finset (Fin n → Fin (2 ^ 64)) := fun ij =>
    Finset.univ.filter (fun x => |fireTime offset delay x ij.1 - fireTime offset delay x ij.2| < δ)
    with hEdef
  have hsub : Finset.univ.filter (fun x => ¬ Uncontested offset delay δ x) ⊆ P.biUnion E := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ (fireTime offset delay x)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    unfold Uncontested at hx
    push Not at hx
    obtain ⟨j, hj, hlt⟩ := hx i0
    have hle := hi0 j (Finset.mem_univ _)
    simp only [Finset.mem_biUnion, hPdef, hEdef, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases lt_or_gt_of_ne hj with h | h
    · exact ⟨(j, i0), h, by rw [abs_lt]; dsimp only; constructor <;> omega⟩
    · exact ⟨(i0, j), h, by rw [abs_lt]; dsimp only; constructor <;> omega⟩
  have hcount : (Finset.univ.filter (fun x => ¬ Uncontested offset delay δ x)).card ≤
      n.choose 2 * ((2 ^ 64) ^ (n - 1) * ((2 * δ - 1) * K)) := by
    calc _ ≤ (P.biUnion E).card := Finset.card_le_card hsub
      _ ≤ ∑ ij ∈ P, (E ij).card := Finset.card_biUnion_le
      _ ≤ ∑ _ij ∈ P, (2 ^ 64) ^ (n - 1) * ((2 * δ - 1) * K) := by
          apply Finset.sum_le_sum
          intro ij hij
          simp only [hPdef, Finset.mem_filter, Finset.mem_univ, true_and] at hij
          exact card_pair_close_le_abstract n δ K hδ offset delay hpre ij.1 ij.2 (ne_of_lt hij)
      _ = _ := by rw [Finset.sum_const, hPdef, card_pairs_lt, smul_eq_mul]
  have hq : ((Finset.univ.filter (fun x => ¬ Uncontested offset delay δ x)).card : ℚ) ≤
      (n.choose 2 : ℚ) * (((2 : ℚ) ^ 64) ^ (n - 1) * (((2 * δ - 1 : ℕ) : ℚ) * K)) := by
    exact_mod_cast hcount
  have hpow : ((2 : ℚ) ^ 64) ^ n = ((2 : ℚ) ^ 64) ^ (n - 1) * 2 ^ 64 := by
    rw [← pow_succ]; congr 1; omega
  rw [div_le_div_iff₀ (by positivity) (by positivity), hpow]
  calc _ ≤ (n.choose 2 : ℚ) * (((2 : ℚ) ^ 64) ^ (n - 1) * (((2 * δ - 1 : ℕ) : ℚ) * K)) * 2 ^ 64 :=
        mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by ring
