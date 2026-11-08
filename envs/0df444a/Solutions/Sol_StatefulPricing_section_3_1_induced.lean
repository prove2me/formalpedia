-- Prove2me | solution 1 for StatefulPricing.section_3_1_induced
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:52:08.710243+00:00
-- url     : https://prove2.me/submissions/0d35f709-64c7-490a-ac5b-0251cf0c4e93

import Mathlib
import Definitions.Def_StatefulPricing_DdMDP
import Definitions.Def_StatefulPricing_Instance
import Definitions.Def_StatefulPricing_Instance_toDdMDP

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Aux_StatefulPricing_s31

open StatefulPricing

theorem demand_spec {T C W : ℕ} (rank : Finset ℕ → ℕ) (I : Instance T C W) (t : ℕ) (p : ℕ → ℝ) :
    I.demand rank t p = ∅ ∨ (I.demand rank t p ⊆ I.active t ∧
      ∀ B ⊆ I.active t, I.utility t p B ≤ I.utility t p (I.demand rank t p)) := by
  classical
  unfold Instance.demand
  dsimp only
  split
  · next h =>
    right
    have hs := (Classical.choose_spec (Finset.exists_min_image _ rank h)).1
    rw [Finset.mem_filter, Finset.mem_powerset] at hs
    refine ⟨hs.1, fun B hB => ?_⟩
    exact hs.2 B (Finset.mem_powerset.mpr hB)
  · left; rfl

theorem pay_unit {T C W : ℕ} (rank : Finset ℕ → ℕ) (I : Instance T C W) (t : ℕ) (x : ℕ → ℝ)
    (hx : ∀ i, 0 < x i ∧ x i ≤ 1) : 0 ≤ I.pay rank t x ∧ I.pay rank t x ≤ 1 := by
  unfold Instance.pay
  refine ⟨Finset.sum_nonneg (fun i _ => (hx i).1.le), ?_⟩
  rcases demand_spec rank I t x with h | ⟨hsub, hmax⟩
  · rw [h, Finset.sum_empty]; norm_num
  · set D := I.demand rank t x
    rcases D.eq_empty_or_nonempty with hD | ⟨i, hi⟩
    · rw [hD, Finset.sum_empty]; norm_num
    · have hia := hsub hi
      unfold Instance.active at hia
      rw [Finset.mem_filter] at hia
      have h1 : 1 ≤ t := le_trans (I.one_le_ta i hia.1) hia.2.1
      have h2 : t ≤ T := le_trans hia.2.2 (I.te_le_T i hia.1)
      have hu := hmax ∅ (Finset.empty_subset _)
      unfold Instance.utility at hu
      rw [I.v_empty, Finset.sum_empty] at hu
      have hv := I.v_lt_one t h1 h2 D hsub
      linarith

end Aux_StatefulPricing_s31

open StatefulPricing in
theorem solution {T C W : ℕ} (rank : Finset ℕ → ℕ) (I : Instance T C W) :
    (I.toDdMDP rank).RewardsInUnit ∧
    (∀ γ : Policy, ∀ t, 1 ≤ t →
      (I.toDdMDP rank).simState γ t = (I.active t, I.policyInv rank γ t)) ∧
    (∀ γ : Policy, (I.toDdMDP rank).policyReward γ T = I.policyRevenue rank γ) ∧
    (∀ p : ℕ → ℕ → ℝ,
      (∀ t, 1 ≤ t → (I.toDdMDP rank).actState p t = (I.active t, I.traj rank (fun s _ => p s) t)) ∧
      ∑ t ∈ Finset.Icc 1 T, (I.toDdMDP rank).f t ((I.toDdMDP rank).actState p t) (p t)
        = I.ruleRevenue rank (fun s _ => p s)) := by
  have hsim : ∀ γ : Policy, ∀ n : ℕ, (I.toDdMDP rank).simState γ (n+1)
      = (I.active (n+1), I.policyInv rank γ (n+1)) := by
    intro γ n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show n + 1 + 1 = n + 2 from rfl, DdMDP.simState, ih]
      rfl
  have hsim' : ∀ γ : Policy, ∀ t, 1 ≤ t →
      (I.toDdMDP rank).simState γ t = (I.active t, I.policyInv rank γ t) := by
    intro γ t ht
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    exact hsim γ n
  have hact : ∀ p : ℕ → ℕ → ℝ, ∀ n : ℕ, (I.toDdMDP rank).actState p (n+1)
      = (I.active (n+1), I.traj rank (fun s _ => p s) (n+1)) := by
    intro p n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show n + 1 + 1 = n + 2 from rfl, DdMDP.actState, ih]
      rfl
  refine ⟨?_, hsim', ?_, ?_⟩
  · intro t s x hx
    exact Aux_StatefulPricing_s31.pay_unit rank I t x hx.1
  · intro γ
    unfold DdMDP.policyReward Instance.policyRevenue Instance.ruleRevenue
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.mem_Icc] at ht
    rw [hsim' γ t ht.1]
    rfl
  · intro p
    refine ⟨fun t ht => ?_, rfl⟩
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    exact hact p n
