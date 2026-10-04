-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.departure_rate_positivity_propagates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:55:13.051336+00:00
-- url     : https://prove2.me/submissions/6021348d-0667-48cd-84e9-0c6ee468444e

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel

open ProcessingNetworks.ProportionalFairness

theorem solution
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha) (hα : ∀ i, 0 < alpha i)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) (hsol : IsPFFluidModelSolution dat Ah Dh Th Zh)
    (t : ℝ) (ht : 0 < t) (hreg : RegularPoint Ah Dh Th Zh t)
    (hpos : ∀ i, 0 < Zh t i → 0 < deriv (fun s => Dh s i) t) :
    ∀ i, 0 < deriv (fun s => Dh s i) t := by
  obtain ⟨hZeq, hZnn, hAeq, hDeq, ⟨-, hTmono, -⟩, -⟩ := hsol
  obtain ⟨-, hDd, -, hZd⟩ := hreg
  have hDdi : ∀ k, DifferentiableAt ℝ (fun s => Dh s k) t := differentiableAt_pi.mp hDd
  have hZdi : ∀ k, DifferentiableAt ℝ (fun s => Zh s k) t := differentiableAt_pi.mp hZd
  set d : Fin I → ℝ := fun k => deriv (fun s => Dh s k) t with hd
  -- nonnegativity of the departure rates
  have hdnn : ∀ k, 0 ≤ d k := by
    intro k
    have heq : (fun s => Dh s k) =ᶠ[nhds t] (fun s => Th s k / dat.m k) := by
      filter_upwards [lt_mem_nhds ht] with s hs
      exact hDeq s hs.le k
    have hmono : Monotone (fun s => Th s k / dat.m k) := fun a b hab =>
      div_le_div_of_nonneg_right (hTmono hab k) (dat.hm k).le
    simp only [hd]
    rw [heq.deriv_eq]
    exact hmono.deriv_nonneg
  -- derivative of Z_i
  have hZder : ∀ i, deriv (fun s => Zh s i) t = dat.lam i + ∑ k, dat.P k i * d k - d i := by
    intro i
    have heq : (fun s => Zh s i) =ᶠ[nhds t]
        (fun s => Zh 0 i + (dat.lam i * s + ∑ k, dat.P k i * Dh s k) - Dh s i) := by
      filter_upwards [lt_mem_nhds ht] with s hs
      rw [hZeq s hs.le]
      beta_reduce
      rw [hAeq s hs.le i]
    rw [heq.deriv_eq]
    have h1 : HasDerivAt (fun s => Zh 0 i + (dat.lam i * s + ∑ k, dat.P k i * Dh s k) - Dh s i)
        (0 + (dat.lam i * 1 + ∑ k, dat.P k i * d k) - d i) t := by
      refine ((hasDerivAt_const t _).add (((hasDerivAt_id t).const_mul _).add ?_)).sub
        (hDdi i).hasDerivAt
      exact HasDerivAt.fun_sum fun k _ => ((hDdi k).hasDerivAt).const_mul _
    rw [h1.deriv]; ring
  -- the set of classes with zero departure rate
  have hU : ∀ i, d i ≤ 0 → dat.lam i = 0 ∧ ∀ k, 0 < dat.P k i → d k ≤ 0 := by
    intro i hi
    have hZi : Zh t i = 0 := by
      by_contra hne
      have := hpos i (lt_of_le_of_ne (hZnn t ht.le i) (Ne.symm hne))
      simp only [hd] at hi
      linarith
    have hmin : IsLocalMin (fun s => Zh s i) t := by
      filter_upwards [lt_mem_nhds ht] with s hs
      rw [hZi]; exact hZnn s hs.le i
    have h0 := hmin.deriv_eq_zero
    rw [hZder i] at h0
    have hdi : d i = 0 := le_antisymm hi (hdnn i)
    rw [hdi, sub_zero] at h0
    have hterm : ∀ k, 0 ≤ dat.P k i * d k := fun k => mul_nonneg (hP_nonneg k i) (hdnn k)
    have hsum : 0 ≤ ∑ k, dat.P k i * d k := Finset.sum_nonneg fun k _ => hterm k
    refine ⟨by linarith [hlam i], fun k hk => ?_⟩
    have hle : dat.P k i * d k ≤ ∑ k, dat.P k i * d k :=
      Finset.single_le_sum (fun k _ => hterm k) (Finset.mem_univ k)
    have : dat.P k i * d k ≤ 0 := by linarith [hlam i]
    by_contra hdk
    push_neg at hdk
    nlinarith [mul_pos hk hdk]
  -- v = α on U, 0 elsewhere
  set v : Fin I → ℝ := fun i => if d i ≤ 0 then alpha i else 0 with hv
  have hvnn : ∀ i, 0 ≤ v i := fun i => by simp only [hv]; split_ifs <;> linarith [hα i]
  have hvsub : ∀ i, v i ≤ ∑ k, dat.P k i * v k := by
    intro i
    simp only [hv]
    split_ifs with hi
    · obtain ⟨hl, hk⟩ := hU i hi
      have hai : alpha i = dat.lam i + ∑ k, dat.P k i * alpha k := congrFun halpha i
      rw [hai, hl, zero_add]
      refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
      split_ifs with hdk
      · rfl
      · rcases (hP_nonneg k i).lt_or_eq with hpk | hpk
        · exact absurd (hk k hpk) hdk
        · rw [← hpk]; simp
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (hP_nonneg k i) (hvnn k)
  have hiter : ∀ n i, v i ≤ ∑ k, (dat.P ^ n) k i * v k := by
    intro n
    induction n with
    | zero => intro i; simp [Matrix.one_apply]
    | succ n ih =>
      intro i
      calc v i ≤ ∑ k, dat.P k i * v k := hvsub i
        _ ≤ ∑ k, dat.P k i * ∑ l, (dat.P ^ n) l k * v l :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (ih k) (hP_nonneg k i)
        _ = ∑ l, (dat.P ^ (n + 1)) l i * v l := by
          rw [pow_succ]
          simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
          ring
  have hlim : ∀ i, Filter.Tendsto (fun n => ∑ k, (dat.P ^ n) k i * v k) Filter.atTop (nhds 0) := by
    intro i
    have := tendsto_finset_sum (Finset.univ : Finset (Fin I))
      (fun k _ => (hP_transient k i).mul_const (v k))
    simpa using this
  intro i
  by_contra hneg
  push_neg at hneg
  have hvi : v i = alpha i := by simp only [hv]; rw [if_pos hneg]
  have := ge_of_tendsto (hlim i) (Filter.Eventually.of_forall fun n => hiter n i)
  linarith [hα i]


