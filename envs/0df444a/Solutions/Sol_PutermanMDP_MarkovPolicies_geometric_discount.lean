-- Prove2me | solution 1 for PutermanMDP.MarkovPolicies.geometric_discount
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:21:00.550987+00:00
-- url     : https://prove2.me/submissions/51ee1fe1-26ce-4a63-ab0a-0dbbf5d860ec

import Mathlib
import Definitions.Def_PutermanMDP_MarkovPolicies_RewardCriteria

open Filter Topology
open PutermanMDP.MarkovPolicies

theorem pmf_hasSum_toReal_one' {X : Type*} (p : PMF X) : HasSum (fun x => (p x).toReal) 1 := by
  have h := ENNReal.hasSum_toReal (f := fun x => p x) (PMF.tsum_coe_ne_top p)
  rw [← ENNReal.tsum_toReal_eq (fun a => PMF.apply_ne_top p a), PMF.tsum_coe] at h
  simpa using h

theorem solution {S A : Type*} [Countable S] [Nonempty S]
    (M : Model S A) (hM : RewardBounded M) (π : HistoryPolicy M)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∀ s : S, geometricReturn M π (PMF.pure s) β =
      discountedReturn M π (PMF.pure s) β := by
  intro s0
  set μ := PMF.pure s0
  obtain ⟨C, hC0, hC⟩ := hM
  set e : ℕ → ℝ := fun t => expectedReward M π μ t with he
  -- bound on expected rewards
  have hebd : ∀ t, |e t| ≤ C := by
    intro t
    have hg : HasSum (fun z => (stateActionLaw M π μ t z).toReal * C) C := by
      simpa using (pmf_hasSum_toReal_one' (stateActionLaw M π μ t)).mul_right C
    have := tsum_of_norm_bounded
      (f := fun z : S × A => (stateActionLaw M π μ t z).toReal * M.reward z.1 z.2) hg (by
        intro z
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        by_cases hz : stateActionLaw M π μ t z = 0
        · rw [hz]; simp
        · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          have hmem : z ∈ (stateActionLaw M π μ t).support := hz
          unfold stateActionLaw at hmem
          rw [PMF.mem_support_bind_iff] at hmem
          obtain ⟨h, _, hh⟩ := hmem
          rw [PMF.mem_support_map_iff] at hh
          obtain ⟨a, _, rfl⟩ := hh
          exact hC _ _ a.property)
    simpa [Real.norm_eq_abs, he, expectedReward] using this
  have hfin : ∀ N, finiteReturn M π μ N = ∑ t ∈ Finset.range N, e t := fun N => rfl
  have hfinbd : ∀ N, |finiteReturn M π μ N| ≤ N * C := by
    intro N
    rw [hfin]
    calc _ ≤ ∑ t ∈ Finset.range N, |e t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.range N, C := Finset.sum_le_sum (fun t _ => hebd t)
      _ = N * C := by simp
  -- partial sum identity
  have ident : ∀ N, ∑ n ∈ Finset.range N, ((1 - β) * β ^ n) * finiteReturn M π μ (n + 1)
      = ∑ n ∈ Finset.range N, β ^ n * e n - β ^ N * finiteReturn M π μ N := by
    intro N
    induction N with
    | zero => simp [hfin]
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hfin (N + 1),
        Finset.sum_range_succ, ← hfin N, pow_succ]
      ring
  have hβabs : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1
  have sumA : Summable (fun n : ℕ => ((1 - β) * β ^ n) * finiteReturn M π μ (n + 1)) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => ((1 - β) * C) * ((n : ℝ) ^ 1 * β ^ n + β ^ n))
      (((summable_pow_mul_geometric_of_norm_lt_one 1 hβabs).add
        (summable_geometric_of_lt_one hβ0 hβ1)).mul_left _) ?_
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by have := pow_nonneg hβ0 n; nlinarith)]
    have h1 := hfinbd (n + 1)
    have hp := pow_nonneg hβ0 n
    have : 0 ≤ (1 - β) * β ^ n := by nlinarith
    calc (1 - β) * β ^ n * |finiteReturn M π μ (n + 1)|
        ≤ (1 - β) * β ^ n * (((n + 1 : ℕ) : ℝ) * C) := mul_le_mul_of_nonneg_left h1 this
      _ = _ := by push_cast; ring
  have sumB : Summable (fun n : ℕ => β ^ n * e n) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => C * β ^ n)
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_left C) ?_
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 n)]
    have := mul_le_mul_of_nonneg_left (hebd n) (pow_nonneg hβ0 n)
    linarith
  have tA := sumA.hasSum.tendsto_sum_nat
  have tB := sumB.hasSum.tendsto_sum_nat
  have tR : Tendsto (fun N : ℕ => β ^ N * finiteReturn M π μ N) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => C * ((N : ℝ) * β ^ N))
    · intro N
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 N)]
      have := mul_le_mul_of_nonneg_left (hfinbd N) (pow_nonneg hβ0 N)
      nlinarith
    · simpa using (tendsto_self_mul_const_pow_of_lt_one hβ0 hβ1).const_mul C
  have tA' : Tendsto (fun N => ∑ n ∈ Finset.range N, ((1 - β) * β ^ n) *
      finiteReturn M π μ (n + 1)) atTop (𝓝 (∑' n : ℕ, β ^ n * e n - 0)) := by
    simp only [ident]
    exact tB.sub tR
  unfold geometricReturn discountedReturn
  rw [sub_zero] at tA'
  exact tendsto_nhds_unique tA tA'
