-- Prove2me | solution 1 for SupplyChainTheory.disruption_base_stock
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T00:53:53.559671+00:00
-- url     : https://prove2.me/submissions/17384641-5113-42c6-8fc7-8d4c7734704f

import Mathlib
import Definitions.Def_SupplyChainTheory_disruptions

namespace SupplyChainTheory

open Finset

section Disruption

variable {α β : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
include hα0 hα1 hβ0 hβ1

lemma sc10_pmf_nonneg (n : ℕ) : 0 ≤ disruptionPmf α β n := by
  cases n with
  | zero => simp only [disruptionPmf]; positivity
  | succ n =>
    simp only [disruptionPmf]
    have : 0 ≤ 1 - β := by linarith
    positivity

lemma sc10_pmf_succ_hasSum :
    HasSum (fun n => disruptionPmf α β (n + 1)) (α / (α + β)) := by
  have hr0 : 0 ≤ 1 - β := by linarith
  have hr1 : 1 - β < 1 := by linarith
  have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (α * β / (α + β))
  have e : α / (α + β) = α * β / (α + β) * (1 - (1 - β))⁻¹ := by
    rw [sub_sub_cancel]
    have : α + β ≠ 0 := by linarith
    field_simp
  rw [e]
  exact this

lemma sc10_pmf_hasSum : HasSum (disruptionPmf α β) 1 := by
  have e : (1 : ℝ) - ∑ i ∈ range 1, disruptionPmf α β i = α / (α + β) := by
    simp only [Finset.range_one, Finset.sum_singleton, disruptionPmf]
    have : α + β ≠ 0 := by linarith
    field_simp
    ring
  exact (hasSum_nat_add_iff' 1).1 (by rw [e]; exact sc10_pmf_succ_hasSum hα0 hα1 hβ0 hβ1)

lemma sc10_cdf (n : ℕ) : disruptionCdf α β n = 1 - α / (α + β) * (1 - β) ^ n := by
  induction n with
  | zero => simp [disruptionCdf, disruptionPmf]; field_simp; ring
  | succ n ih =>
    unfold disruptionCdf at ih ⊢
    rw [Finset.sum_range_succ, ih]
    simp only [disruptionPmf]
    field_simp
    ring

end Disruption

/-! ### The newsvendor cost with disruptions -/

lemma sc10_periodCost_nonneg {h p d S : ℝ} (hh : 0 < h) (hp : 0 < p) (n : ℕ) :
    0 ≤ periodCost h p d S n := by
  unfold periodCost
  have := le_max_right (S - (n + 1) * d) 0
  have := le_max_right ((n + 1) * d - S) 0
  positivity

lemma sc10_periodCost_le {h p d S : ℝ} (hh : 0 < h) (hp : 0 < p) (hd : 0 < d) (n : ℕ) :
    periodCost h p d S n ≤ (h + p) * (|S| + d) + (h + p) * d * n := by
  unfold periodCost
  have h1 : max (S - (n + 1) * d) 0 ≤ |S| + d + d * n := by
    apply max_le
    · have := le_abs_self S
      have : (0 : ℝ) ≤ (n : ℝ) * d := by positivity
      nlinarith
    · have : (0 : ℝ) ≤ (n : ℝ) * d := by positivity
      have := abs_nonneg S
      nlinarith
  have h2 : max ((n + 1) * d - S) 0 ≤ |S| + d + d * n := by
    apply max_le
    · have := neg_abs_le S
      nlinarith
    · have : (0 : ℝ) ≤ (n : ℝ) * d := by positivity
      have := abs_nonneg S
      nlinarith
  nlinarith

lemma sc10_summable {α β h p d : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (hp : 0 < p) (hd : 0 < d) (S : ℝ) (w : ℕ → ℝ)
    (hw : ∀ n, |w n| ≤ (h + p) * (|S| + d) + (h + p) * d * n) :
    Summable (fun n => disruptionPmf α β n * w n) := by
  rw [← summable_nat_add_iff 1]
  have hr0 : 0 ≤ 1 - β := by linarith
  have hr1 : 1 - β < 1 := by linarith
  have hg : Summable (fun n : ℕ => (1 - β) ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hg1 : Summable (fun n : ℕ => (n : ℝ) * (1 - β) ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := 1 - β)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    simpa using this
  set A := (h + p) * (|S| + d) + (h + p) * d
  set B := (h + p) * d
  have hbound : Summable (fun n : ℕ => α * β / (α + β) * ((1 - β) ^ n * A + B * ((n : ℝ) * (1 - β) ^ n))) :=
    ((hg.mul_right A).add (hg1.mul_left B)).mul_left _
  refine Summable.of_norm_bounded hbound (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  simp only [disruptionPmf]
  have hc : 0 ≤ α * β / (α + β) * (1 - β) ^ n := by positivity
  rw [abs_of_nonneg hc]
  have := hw (n + 1)
  push_cast at this
  have hpow : 0 ≤ (1 - β) ^ n := by positivity
  have hc0 : 0 ≤ α * β / (α + β) := by positivity
  calc α * β / (α + β) * (1 - β) ^ n * |w (n + 1)|
      ≤ α * β / (α + β) * (1 - β) ^ n * ((h + p) * (|S| + d) + (h + p) * d * ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left this hc
    _ = α * β / (α + β) * ((1 - β) ^ n * A + B * ((n : ℝ) * (1 - β) ^ n)) := by
        simp only [A, B]; ring

/-- Subgradient inequalities for a single period's cost. -/
lemma sc10_subgrad {h p d : ℝ} (hh : 0 < h) (hp : 0 < p) (S T : ℝ) (n : ℕ) :
    periodCost h p d T n + (if (n + 1) * d ≤ T then h else -p) * (S - T) ≤ periodCost h p d S n
      ∧ periodCost h p d T n + (if (n + 1) * d < T then h else -p) * (S - T)
          ≤ periodCost h p d S n := by
  unfold periodCost
  have a1 := le_max_left (S - (n + 1) * d) 0
  have a2 := le_max_right (S - (n + 1) * d) 0
  have a3 := le_max_left ((n + 1) * d - S) 0
  have a4 := le_max_right ((n + 1) * d - S) 0
  constructor
  · split_ifs with hc
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; nlinarith
  · split_ifs with hc
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; nlinarith

/-- The base-stock theorem (Theorem 9.5): `d + d k` is the least global minimizer. -/
lemma sc10_base_stock (α β h p d : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hh : 0 < h) (hp : 0 < p) (hd : 0 < d) (k : ℕ)
    (hk : p / (p + h) ≤ disruptionCdf α β k) (hk' : ∀ n < k, disruptionCdf α β n < p / (p + h)) :
    IsMinOn (meanCost α β h p d) Set.univ (d + d * k)
      ∧ ∀ S, IsMinOn (meanCost α β h p d) Set.univ S → d + d * k ≤ S := by
  set T := d + d * k with hT
  have hsum : ∀ S, Summable (fun n => disruptionPmf α β n * periodCost h p d S n) := fun S =>
    sc10_summable hα0 hα1 hβ0 hβ1 hh hp hd S _ (fun n => by
      rw [abs_of_nonneg (sc10_periodCost_nonneg hh hp n)]; exact sc10_periodCost_le hh hp hd n)
  have hπ := sc10_pmf_hasSum hα0 hα1 hβ0 hβ1
  have hπ0 := sc10_pmf_nonneg hα0 hα1 hβ0 hβ1
  -- the expected subgradient
  have hsg : ∀ (P : ℕ → Prop) [DecidablePred P] (K : ℕ), (∀ n, P n ↔ n < K) →
      HasSum (fun n => disruptionPmf α β n * (if P n then h else -p))
        ((h + p) * (∑ n ∈ range K, disruptionPmf α β n) - p) := by
    intro P _ K hPK
    have e : (fun n => disruptionPmf α β n * (if P n then h else -p))
        = fun n => disruptionPmf α β n * (-p) + (if n ∈ range K then disruptionPmf α β n * (h + p) else 0) := by
      funext n
      by_cases hn : n < K
      · rw [if_pos ((hPK n).2 hn), if_pos (Finset.mem_range.2 hn)]; ring
      · rw [if_neg (fun h => hn ((hPK n).1 h)), if_neg (fun h => hn (Finset.mem_range.1 h))]; ring
    rw [e]
    have h2 : HasSum (fun n => if n ∈ range K then disruptionPmf α β n * (h + p) else 0)
        (∑ n ∈ range K, if n ∈ range K then disruptionPmf α β n * (h + p) else 0) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => if_neg hn)
    rw [Finset.sum_congr rfl (fun n hn => if_pos hn)] at h2
    have h3 := (hπ.mul_right (-p)).add h2
    have e2 : (h + p) * (∑ n ∈ range K, disruptionPmf α β n) - p
        = 1 * -p + ∑ n ∈ range K, disruptionPmf α β n * (h + p) := by
      rw [← Finset.sum_mul]; ring
    rw [e2]
    exact h3
  have hlow : ∀ (P : ℕ → Prop) [DecidablePred P] (K : ℕ), (∀ n, P n ↔ n < K) →
      (∀ S n, periodCost h p d T n + (if P n then h else -p) * (S - T) ≤ periodCost h p d S n) →
      ∀ S, meanCost α β h p d T + ((h + p) * (∑ n ∈ range K, disruptionPmf α β n) - p) * (S - T)
        ≤ meanCost α β h p d S := by
    intro P _ K hPK hsub S
    unfold meanCost
    have hs := (hsg P K hPK).mul_right (S - T)
    rw [← hs.tsum_eq, ← (hsum T).tsum_add hs.summable]
    refine Summable.tsum_le_tsum (fun n => ?_) ((hsum T).add hs.summable) (hsum S)
    have := hsub S n
    have := hπ0 n
    calc disruptionPmf α β n * periodCost h p d T n
          + disruptionPmf α β n * (if P n then h else -p) * (S - T)
        = disruptionPmf α β n * (periodCost h p d T n + (if P n then h else -p) * (S - T)) := by ring
      _ ≤ disruptionPmf α β n * periodCost h p d S n := mul_le_mul_of_nonneg_left (hsub S n) (hπ0 n)
  have hle : ∀ n : ℕ, ((n : ℝ) + 1) * d ≤ T ↔ n < k + 1 := by
    intro n
    rw [hT]
    constructor
    · intro h1
      have : (n : ℝ) + 1 ≤ 1 + k := by
        have := (mul_le_mul_iff_of_pos_right hd).1 (by linarith : ((n : ℝ) + 1) * d ≤ (1 + k) * d)
        exact this
      have : (n : ℝ) ≤ k := by linarith
      have : n ≤ k := by exact_mod_cast this
      omega
    · intro h1
      have : (n : ℝ) ≤ k := by exact_mod_cast (by omega : n ≤ k)
      nlinarith
  have hlt : ∀ n : ℕ, ((n : ℝ) + 1) * d < T ↔ n < k := by
    intro n
    rw [hT]
    constructor
    · intro h1
      have : (n : ℝ) + 1 < 1 + k := by
        by_contra hc; push Not at hc; nlinarith
      have : (n : ℝ) < k := by linarith
      exact_mod_cast this
    · intro h1
      have : (n : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : n + 1 ≤ k)
      nlinarith
  have hA := hlow (fun n => ((n : ℝ) + 1) * d ≤ T) (k + 1) hle (fun S n => (sc10_subgrad hh hp S T n).1)
  have hB := hlow (fun n => ((n : ℝ) + 1) * d < T) k hlt (fun S n => (sc10_subgrad hh hp S T n).2)
  have hFk : ∑ n ∈ range (k + 1), disruptionPmf α β n = disruptionCdf α β k := rfl
  have hcoefA : 0 ≤ (h + p) * disruptionCdf α β k - p := by
    have := (div_le_iff₀ (by linarith : 0 < p + h)).1 hk
    linarith
  have hcoefB : (h + p) * (∑ n ∈ range k, disruptionPmf α β n) - p < 0 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp; linarith
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have := (lt_div_iff₀ (by linarith : 0 < p + h)).1 (hk' k' (by omega))
      have e : ∑ n ∈ range (k' + 1), disruptionPmf α β n = disruptionCdf α β k' := rfl
      rw [e]; linarith
  have hmin : ∀ S, meanCost α β h p d T ≤ meanCost α β h p d S := by
    intro S
    rcases le_or_gt T S with hS | hS
    · have := hA S; rw [hFk] at this; nlinarith
    · have := hB S; nlinarith
  refine ⟨isMinOn_iff.2 (fun S _ => hmin S), fun S hS => ?_⟩
  by_contra hlt'
  push Not at hlt'
  have h1 := isMinOn_iff.1 hS T (Set.mem_univ _)
  have h2 := hB S
  nlinarith

end SupplyChainTheory

open SupplyChainTheory

theorem solution (α β h p d : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hh : 0 < h) (hp : 0 < p) (hd : 0 < d) (k : ℕ)
    (hk : p / (p + h) ≤ disruptionCdf α β k) (hk' : ∀ n < k, disruptionCdf α β n < p / (p + h)) :
    IsMinOn (meanCost α β h p d) Set.univ (d + d * k)
      ∧ ∀ S, IsMinOn (meanCost α β h p d) Set.univ S → d + d * k ≤ S :=
  sc10_base_stock α β h p d hα0 hα1 hβ0 hβ1 hh hp hd k hk hk'
