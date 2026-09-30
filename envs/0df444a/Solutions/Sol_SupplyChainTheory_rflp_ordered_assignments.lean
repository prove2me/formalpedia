-- Prove2me | solution 1 for SupplyChainTheory.rflp_ordered_assignments
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T00:53:55.222361+00:00
-- url     : https://prove2.me/submissions/2e79656d-f114-4e77-9ad4-8ae9c994f32e

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

namespace SupplyChainTheory

open Finset

/-- A sum changes only by the corrections at two points where the families differ. -/
lemma sc10_sum_two {m : ℕ} (S : Finset (Fin m)) (g g' : Fin m → ℝ) (r r' : Fin m) (hrr : r ≠ r')
    (hsame : ∀ t, t ≠ r → t ≠ r' → g' t = g t) :
    ∑ t ∈ S, g' t = ∑ t ∈ S, g t + (if r ∈ S then g' r - g r else 0)
      + (if r' ∈ S then g' r' - g r' else 0) := by
  have e : ∀ t, g' t = g t + ((if t = r then g' r - g r else 0) + (if t = r' then g' r' - g r' else 0)) := by
    intro t
    by_cases h1 : t = r
    · subst h1; simp [hrr]
    · by_cases h2 : t = r'
      · subst h2; simp [h1]
      · simp [h1, h2, hsame t h1 h2]
  rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  ring

lemma sc10_cost_diff {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ) (q : ℝ)
    (u : Fin m) (x : Fin m → ℝ) (y y' : Fin n → Fin m → Fin m → ℝ) (i : Fin n) (r r' : Fin m)
    (hrr : r ≠ r')
    (hsame : ∀ i' j' s, (i' ≠ i ∨ (s ≠ r ∧ s ≠ r')) → y' i' j' s = y i' j' s) :
    rflpCost h c f q u x y' = rflpCost h c f q u x y
      + ∑ j', rflpPsi h c q u i j' r.val * (y' i j' r - y i j' r)
      + ∑ j', rflpPsi h c q u i j' r'.val * (y' i j' r' - y i j' r') := by
  unfold rflpCost
  have hi : ∀ i', i' ≠ i → ∑ j, ∑ s : Fin m, rflpPsi h c q u i' j s.val * y' i' j s
      = ∑ j, ∑ s : Fin m, rflpPsi h c q u i' j s.val * y i' j s := by
    intro i' hi'
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro s _
    rw [hsame i' j s (Or.inl hi')]
  have hii : ∑ j, ∑ s : Fin m, rflpPsi h c q u i j s.val * y' i j s
      = ∑ j, ∑ s : Fin m, rflpPsi h c q u i j s.val * y i j s
        + ∑ j', rflpPsi h c q u i j' r.val * (y' i j' r - y i j' r)
        + ∑ j', rflpPsi h c q u i j' r'.val * (y' i j' r' - y i j' r') := by
    rw [add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    have := sc10_sum_two univ (fun s => rflpPsi h c q u i j s.val * y i j s)
      (fun s => rflpPsi h c q u i j s.val * y' i j s) r r' hrr
      (fun t h1 h2 => by rw [hsame i j t (Or.inr ⟨h1, h2⟩)])
    simp only [Finset.mem_univ, if_true] at this
    rw [this]; ring
  rw [← Finset.add_sum_erase univ _ (mem_univ i), ← Finset.add_sum_erase univ _ (mem_univ i),
    Finset.sum_congr rfl (fun i' hi' => hi i' (Finset.ne_of_mem_erase hi')), hii]
  ring

lemma sc10_sum_indicator {m : ℕ} (w : Fin m → ℝ) (a : Fin m) :
    ∑ j', w j' * (if j' = a then (1 : ℝ) else 0) = w a := by
  simp

end SupplyChainTheory

open SupplyChainTheory Finset

theorem solution {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (q : ℝ) (u : Fin m) (hq0 : 0 < q) (hq1 : q < 1) (hh : ∀ i, 0 < h i)
    (x : Fin m → ℝ) (y : Fin n → Fin m → Fin m → ℝ) (hopt : RFLPOptimal h c f q u x y)
    (i : Fin n) (j k : Fin m) (r r' : Fin m) (hr : r.val + 2 < m) (hr' : r'.val = r.val + 1)
    (hj : y i j r = 1) (hk : y i k r' = 1) : c i j ≤ c i k := by
  classical
  obtain ⟨⟨hlev, hyx, hone, hxu, hxb, hyb⟩, hmin⟩ := hopt
  have hy0 : ∀ i j r, 0 ≤ y i j r := fun i j r => by
    rcases hyb i j r with h | h <;> rw [h] <;> norm_num
  have hx0 : ∀ j, 0 ≤ x j := fun j => by rcases hxb j with h | h <;> rw [h] <;> norm_num
  have hrr : r < r' := by rw [Fin.lt_def]; omega
  have hrr' : r ≠ r' := ne_of_lt hrr
  have hothers : ∀ (a : Fin m → ℝ), (∀ j, 0 ≤ a j) → ∑ j, a j ≤ 1 → ∀ j0, a j0 = 1 →
      ∀ j', j' ≠ j0 → a j' = 0 := by
    intro a ha hs j0 hj0 j' hj'
    have e := Finset.add_sum_erase univ a (mem_univ j0)
    have h2 : a j' ≤ ∑ l ∈ univ.erase j0, a l :=
      Finset.single_le_sum (fun l _ => ha l) (Finset.mem_erase.2 ⟨hj', mem_univ _⟩)
    linarith [ha j']
  have hEsum : ∀ s, 0 ≤ ∑ s' ∈ univ.filter (fun s' : Fin m => s' < s), y i u s' :=
    fun s => Finset.sum_nonneg (fun _ _ => hy0 _ _ _)
  have hlevle : ∀ s, ∑ j', y i j' s ≤ 1 := fun s => by have := hlev i s; linarith [hEsum s]
  have hr0 : ∀ j', j' ≠ j → y i j' r = 0 :=
    hothers (fun j' => y i j' r) (fun _ => hy0 _ _ _) (hlevle r) j hj
  have hr'0 : ∀ j', j' ≠ k → y i j' r' = 0 :=
    hothers (fun j' => y i j' r') (fun _ => hy0 _ _ _) (hlevle r') k hk
  have hEr : ∑ s' ∈ univ.filter (fun s' : Fin m => s' < r), y i u s' = 0 := by
    have := hlev i r
    have hge : 1 ≤ ∑ j', y i j' r := by
      rw [← hj]; exact Finset.single_le_sum (f := fun j' => y i j' r) (fun _ _ => hy0 _ _ _) (mem_univ j)
    linarith [hEsum r]
  have hEr' : ∑ s' ∈ univ.filter (fun s' : Fin m => s' < r'), y i u s' = 0 := by
    have := hlev i r'
    have hge : 1 ≤ ∑ j', y i j' r' := by
      rw [← hk]; exact Finset.single_le_sum (f := fun j' => y i j' r') (fun _ _ => hy0 _ _ _) (mem_univ k)
    linarith [hEsum r']
  have hju : j ≠ u := by
    intro hju; subst hju
    have : y i j r ≤ ∑ s' ∈ univ.filter (fun s' : Fin m => s' < r'), y i j s' :=
      Finset.single_le_sum (f := fun s' => y i j s') (fun _ _ => hy0 _ _ _)
        (Finset.mem_filter.2 ⟨mem_univ _, hrr⟩)
    linarith
  have hjk : j ≠ k := by
    intro hjk; subst hjk
    have h1 := hone i j
    have := sc10_sum_two univ (fun s => (0 : ℝ)) (fun s => y i j s) r r' hrr'
    have h2 : y i j r + y i j r' ≤ ∑ s, y i j s := by
      rw [← Finset.sum_pair hrr']
      exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => hy0 _ _ _)
    linarith
  have hyr : ∀ j', y i j' r = if j' = j then 1 else 0 := by
    intro j'; split_ifs with h1
    · subst h1; exact hj
    · exact hr0 j' h1
  have hyr' : ∀ j', y i j' r' = if j' = k then 1 else 0 := by
    intro j'; split_ifs with h1
    · subst h1; exact hk
    · exact hr'0 j' h1
  have hψ : ∀ l (s : ℕ), rflpPsi h c q u i l s = h i * c i l * q ^ s * (if l = u then 1 else 1 - q) :=
    fun l s => rfl
  have hr'v : r'.val = r.val + 1 := hr'
  have hpos : 0 < h i * q ^ r.val * (1 - q) := by
    have := hh i; have : 0 < 1 - q := by linarith
    positivity
  by_cases hku : k = u
  · -- promote the emergency facility to level `r`
    subst hku
    set y' : Fin n → Fin m → Fin m → ℝ := fun i' j' s =>
      if i' = i ∧ s = r then (if j' = k then 1 else 0) else if i' = i ∧ s = r' then 0 else y i' j' s
      with hy'
    have hsame : ∀ i' j' s, (i' ≠ i ∨ (s ≠ r ∧ s ≠ r')) → y' i' j' s = y i' j' s := by
      intro i' j' s hc
      simp only [hy']
      rcases hc with hc | ⟨h1, h2⟩
      · simp [hc]
      · simp [h1, h2]
    have hy'r : ∀ j', y' i j' r = if j' = k then 1 else 0 := fun j' => by simp [hy']
    have hy'r' : ∀ j', y' i j' r' = 0 := fun j' => by simp [hy', Ne.symm hrr']
    have hfeas : RFLPFeasible k x y' := by
      refine ⟨?_, ?_, ?_, hxu, hxb, ?_⟩
      · intro i' s
        by_cases hi' : i' = i
        · subst hi'
          have hE : ∑ s' ∈ univ.filter (fun s' : Fin m => s' < s), y' i' k s'
              = ∑ s' ∈ univ.filter (fun s' : Fin m => s' < s), y i' k s'
                + (if r ∈ univ.filter (fun s' : Fin m => s' < s) then 1 else 0)
                + (if r' ∈ univ.filter (fun s' : Fin m => s' < s) then -1 else 0) := by
            rw [sc10_sum_two _ (fun s' => y i' k s') (fun s' => y' i' k s') r r' hrr'
              (fun t h1 h2 => hsame i' k t (Or.inr ⟨h1, h2⟩))]
            simp only [hy'r, hy'r', if_true, hk, hr0 k (Ne.symm hju)]
            congr 1 <;> split_ifs <;> ring
          by_cases hs : s = r
          · subst hs
            rw [Finset.sum_congr rfl (fun j' _ => hy'r j'), hE]
            simp [hEr, lt_irrefl, not_lt.2 (le_of_lt hrr)]
          · by_cases hs' : s = r'
            · subst hs'
              rw [Finset.sum_congr rfl (fun j' _ => hy'r' j'), hE]
              simp [hEr', hrr]
            · rw [Finset.sum_congr rfl (fun j' _ => hsame i' j' s (Or.inr ⟨hs, hs'⟩)), hE]
              have := hlev i' s
              rcases lt_or_gt_of_ne hs with hlt | hgt
              · have h1 : ¬ r < s := not_lt.2 (le_of_lt hlt)
                have h2 : ¬ r' < s := not_lt.2 (le_of_lt (lt_trans hlt hrr))
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, h1, h2, if_false]
                linarith
              · have h2 : r' < s := by
                  rw [Fin.lt_def] at hgt ⊢
                  have : s.val ≠ r'.val := fun e => hs' (Fin.ext e)
                  omega
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, hgt, h2, if_true]
                linarith
        · rw [Finset.sum_congr rfl (fun j' _ => hsame i' j' s (Or.inl hi')),
            Finset.sum_congr rfl (fun s' _ => hsame i' k s' (Or.inl hi'))]
          exact hlev i' s
      · intro i' j' s
        by_cases hc : i' = i ∧ s = r
        · obtain ⟨rfl, rfl⟩ := hc
          rw [hy'r]; split_ifs with h1
          · subst h1; rw [hxu]
          · exact hx0 j'
        · by_cases hc' : i' = i ∧ s = r'
          · obtain ⟨rfl, rfl⟩ := hc'
            rw [hy'r']; exact hx0 j'
          · have : i' ≠ i ∨ (s ≠ r ∧ s ≠ r') := by tauto
            rw [hsame i' j' s this]; exact hyx i' j' s
      · intro i' j'
        by_cases hi' : i' = i
        · subst hi'
          rw [sc10_sum_two _ (fun s => y i' j' s) (fun s => y' i' j' s) r r' hrr'
            (fun t h1 h2 => hsame i' j' t (Or.inr ⟨h1, h2⟩))]
          simp only [Finset.mem_univ, if_true, hy'r, hy'r']
          have h1 := hone i' j'
          by_cases hj' : j' = k
          · subst hj'; rw [if_pos rfl, hk, hr0 j' (Ne.symm hju)]; linarith
          · rw [if_neg hj', hr'0 j' hj']
            by_cases hjj : j' = j
            · subst hjj; rw [hj]; linarith
            · rw [hr0 j' hjj]; linarith
        · rw [Finset.sum_congr rfl (fun s _ => hsame i' j' s (Or.inl hi'))]
          exact hone i' j'
      · intro i' j' s
        simp only [hy']
        split_ifs <;> first | left; rfl | right; rfl | exact hyb i' j' s
    have hle := hmin x y' hfeas
    rw [sc10_cost_diff h c f q k x y y' i r r' hrr' hsame] at hle
    simp only [hy'r, hy'r', hyr, hyr'] at hle
    have e1 : ∑ j', rflpPsi h c q k i j' r.val * ((if j' = k then (1 : ℝ) else 0) - if j' = j then 1 else 0)
        = rflpPsi h c q k i k r.val - rflpPsi h c q k i j r.val := by
      simp only [mul_sub, Finset.sum_sub_distrib, sc10_sum_indicator]
    have e2 : ∑ j', rflpPsi h c q k i j' r'.val * ((0 : ℝ) - if j' = k then 1 else 0)
        = -rflpPsi h c q k i k r'.val := by
      simp only [zero_sub, mul_neg, Finset.sum_neg_distrib, sc10_sum_indicator]
    rw [e1, e2, hψ, hψ, hψ, hr'v] at hle
    simp only [eq_self_iff_true, if_true, if_neg hju] at hle
    have : 0 ≤ h i * q ^ r.val * (1 - q) * (c i k - c i j) := by
      have e : h i * q ^ r.val * (1 - q) * (c i k - c i j)
          = h i * c i k * q ^ r.val * 1 - h i * c i j * q ^ r.val * (1 - q)
            - h i * c i k * q ^ (r.val + 1) * 1 := by ring
      rw [e]; linarith
    have := (mul_nonneg_iff_of_pos_left hpos).1 this
    linarith
  · -- swap the two assignments
    set y' : Fin n → Fin m → Fin m → ℝ := fun i' j' s =>
      if i' = i ∧ s = r then (if j' = k then 1 else 0)
      else if i' = i ∧ s = r' then (if j' = j then 1 else 0) else y i' j' s with hy'
    have hsame : ∀ i' j' s, (i' ≠ i ∨ (s ≠ r ∧ s ≠ r')) → y' i' j' s = y i' j' s := by
      intro i' j' s hc
      simp only [hy']
      rcases hc with hc | ⟨h1, h2⟩
      · simp [hc]
      · simp [h1, h2]
    have hy'r : ∀ j', y' i j' r = if j' = k then 1 else 0 := fun j' => by simp [hy']
    have hy'r' : ∀ j', y' i j' r' = if j' = j then 1 else 0 := fun j' => by simp [hy', Ne.symm hrr']
    have hEq : ∀ s', y' i u s' = y i u s' := by
      intro s'
      by_cases h1 : s' = r
      · subst h1; rw [hy'r, if_neg (Ne.symm hku), hr0 u (Ne.symm hju)]
      · by_cases h2 : s' = r'
        · subst h2; rw [hy'r', if_neg (Ne.symm hju), hr'0 u (Ne.symm hku)]
        · exact hsame i u s' (Or.inr ⟨h1, h2⟩)
    have hfeas : RFLPFeasible u x y' := by
      refine ⟨?_, ?_, ?_, hxu, hxb, ?_⟩
      · intro i' s
        by_cases hi' : i' = i
        · subst hi'
          rw [Finset.sum_congr rfl (fun s' _ => hEq s')]
          by_cases hs : s = r
          · subst hs
            rw [Finset.sum_congr rfl (fun j' _ => hy'r j'), hEr]; simp
          · by_cases hs' : s = r'
            · subst hs'
              rw [Finset.sum_congr rfl (fun j' _ => hy'r' j'), hEr']; simp
            · rw [Finset.sum_congr rfl (fun j' _ => hsame i' j' s (Or.inr ⟨hs, hs'⟩))]
              exact hlev i' s
        · rw [Finset.sum_congr rfl (fun j' _ => hsame i' j' s (Or.inl hi')),
            Finset.sum_congr rfl (fun s' _ => hsame i' u s' (Or.inl hi'))]
          exact hlev i' s
      · intro i' j' s
        by_cases hc : i' = i ∧ s = r
        · obtain ⟨rfl, rfl⟩ := hc
          rw [hy'r]; split_ifs with h1
          · subst h1; have := hyx i' j' r'; rw [hk] at this; exact this
          · exact hx0 j'
        · by_cases hc' : i' = i ∧ s = r'
          · obtain ⟨rfl, rfl⟩ := hc'
            rw [hy'r']; split_ifs with h1
            · subst h1; have := hyx i' j' r; rw [hj] at this; exact this
            · exact hx0 j'
          · have : i' ≠ i ∨ (s ≠ r ∧ s ≠ r') := by tauto
            rw [hsame i' j' s this]; exact hyx i' j' s
      · intro i' j'
        by_cases hi' : i' = i
        · subst hi'
          rw [sc10_sum_two _ (fun s => y i' j' s) (fun s => y' i' j' s) r r' hrr'
            (fun t h1 h2 => hsame i' j' t (Or.inr ⟨h1, h2⟩))]
          simp only [Finset.mem_univ, if_true, hy'r, hy'r', hyr, hyr']
          have h1 := hone i' j'
          by_cases h2 : j' = j
          · subst h2; simp [hjk]; linarith
          · by_cases h3 : j' = k
            · subst h3; simp [h2]; linarith
            · simp [h2, h3]; linarith
        · rw [Finset.sum_congr rfl (fun s _ => hsame i' j' s (Or.inl hi'))]
          exact hone i' j'
      · intro i' j' s
        simp only [hy']
        split_ifs <;> first | left; rfl | right; rfl | exact hyb i' j' s
    have hle := hmin x y' hfeas
    rw [sc10_cost_diff h c f q u x y y' i r r' hrr' hsame] at hle
    simp only [hy'r, hy'r', hyr, hyr'] at hle
    have e1 : ∀ (s : ℕ) (a b : Fin m), ∑ j', rflpPsi h c q u i j' s *
        ((if j' = a then (1 : ℝ) else 0) - if j' = b then 1 else 0)
        = rflpPsi h c q u i a s - rflpPsi h c q u i b s := by
      intro s a b
      simp only [mul_sub, Finset.sum_sub_distrib, sc10_sum_indicator]
    rw [e1, e1, hψ, hψ, hψ, hψ, hr'v] at hle
    simp only [if_neg hju, if_neg hku] at hle
    have : 0 ≤ h i * q ^ r.val * (1 - q) * ((1 - q) * (c i k - c i j)) := by
      have e : h i * q ^ r.val * (1 - q) * ((1 - q) * (c i k - c i j))
          = (h i * c i k * q ^ r.val * (1 - q) - h i * c i j * q ^ r.val * (1 - q))
            + (h i * c i j * q ^ (r.val + 1) * (1 - q) - h i * c i k * q ^ (r.val + 1) * (1 - q)) := by
        ring
      rw [e]; linarith
    have h2 := (mul_nonneg_iff_of_pos_left hpos).1 this
    have h3 : 0 < 1 - q := by linarith
    have := (mul_nonneg_iff_of_pos_left h3).1 h2
    linarith
