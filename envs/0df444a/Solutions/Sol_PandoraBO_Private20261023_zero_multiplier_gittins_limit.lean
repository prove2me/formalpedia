-- Prove2me | solution 1 for PandoraBO.Private20261023.zero_multiplier_gittins_limit
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:29:23.302178+00:00
-- url     : https://prove2.me/submissions/a7b392ca-01e1-4fad-8040-38eae8a1fc1e

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_reservation_index_exists_unique
import Theorems.Thm_PandoraBO_Private20261023_reservation_roots_zero_limit
import Theorems.Thm_PandoraBO_Private20261023_finite_index_policy_subsequence_limit
import Theorems.Thm_PandoraBO_Private20261023_optimal_policy_subsequence_limits
import Theorems.Thm_PandoraBO_Private20261023_weitzman_optimality
import Theorems.Thm_PandoraBO_Private20261023_zero_gittins_full_information
import Mathlib.Topology.Instances.EReal.Lemmas

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace PandoraBO.Private20261023.ZeroMultiplierPolicyLimit

theorem zero_policy_limit_core {n : ℕ} (M : Instance n)
    (multipliers : ℕ → ℝ) (hpos : ∀ k, 0 < multipliers k)
    (hmono : Antitone multipliers)
    (hlim : Tendsto multipliers atTop (nhds 0)) :
    ∃ policies : ℕ → Policy n, ∃ π : Policy n,
      (∀ k, isGittinsPolicy M (multipliers k) (policies k)) ∧
      isZeroGittinsPolicy M π ∧
      expectedReward M π = fullInformationReward M ∧
      Tendsto (fun k => expectedCost M (policies k)) atTop (nhds (expectedCost M π)) ∧
      Tendsto (fun k => expectedReward M (policies k)) atTop (nhds (expectedReward M π)) := by
  classical
  have hrootchoice : ∀ i : Box n, ∃ roots : ℕ → ℝ,
      (∀ k, reservationRoot M i (multipliers k * M.cost i) (roots k)) ∧
      Tendsto (fun k => (roots k : EReal)) atTop (nhds (zeroReservationIndex M i)) :=
    fun i => (reservation_roots_zero_limit M i).2.2 multipliers hpos hlim
  choose roots hroots hrootslim using hrootchoice
  let zs : ℕ → Box n → EReal := fun k i => (roots i k : EReal)
  have hbelow : ∀ i k, zs k i ≤ zeroReservationIndex M i := by
    intro i k
    have hEI : 0 < expectedImprovement M i (roots i k) := by
      rw [hroots i k]
      exact mul_pos (hpos k) (M.cost_positive i)
    exact ((reservation_roots_zero_limit M i).2.1 (roots i k) |>.mp hEI).le
  obtain ⟨policies, hsameindex, hpolicies, extraction, π, hextract, hπ, hcost, hreward⟩ :=
    finite_index_policy_subsequence_limit M zs (zeroReservationIndex M) false
      hrootslim hbelow
  have hgittins : ∀ k, isGittinsPolicy M (multipliers k) (policies k) := by
    intro k
    refine ⟨fun i => roots i k, fun i => hroots i k, ?_, ?_⟩
    · simpa only [zs, EReal.coe_le_coe_iff] using (hpolicies k).1
    · intro h u hh
      have hi := (hpolicies k).2 h u hh
      cases hnext : (policies k).next (h,u) with
      | none =>
          simp only [hnext] at hi ⊢
          simpa only [zs, EReal.coe_le_coe_iff] using hi
      | some i =>
          simp only [hnext] at hi ⊢
          simpa only [zs, EReal.coe_le_coe_iff] using hi
  have hsame : ∀ j k, multipliers j = multipliers k → policies j = policies k := by
    intro j k hjk
    apply hsameindex j k
    funext i
    apply congrArg (fun r : ℝ => (r : EReal))
    exact (reservation_index_exists_unique M (multipliers k) (hpos k) i).unique
      (by simpa only [hjk] using hroots i j) (hroots i k)
  have hzero : isZeroGittinsPolicy M π := hπ
  have hlimits := optimal_policy_subsequence_limits M multipliers (fun k => (hpos k).le)
    policies (fun k => (weitzman_optimality M (multipliers k) (hpos k)).2 _ (hgittins k))
    hsame (Or.inr hmono) extraction hextract (expectedCost M π) (expectedReward M π)
    hcost hreward
  exact ⟨policies, π, hgittins, hzero, (zero_gittins_full_information M π hzero).1,
    hlimits.1, hlimits.2⟩

end PandoraBO.Private20261023.ZeroMultiplierPolicyLimit

theorem solution {n : ℕ} (M : PandoraBO.Instance n)
    (multipliers : ℕ → ℝ) (hpos : ∀ k, 0 < multipliers k)
    (hmono : Antitone multipliers)
    (hlim : Tendsto multipliers atTop (nhds 0)) :
    ∃ policies : ℕ → PandoraBO.Policy n, ∃ π : PandoraBO.Policy n,
      (∀ k, PandoraBO.isGittinsPolicy M (multipliers k) (policies k)) ∧
      PandoraBO.isZeroGittinsPolicy M π ∧
      PandoraBO.expectedReward M π = PandoraBO.fullInformationReward M ∧
      Tendsto (fun k => PandoraBO.expectedCost M (policies k)) atTop
        (nhds (PandoraBO.expectedCost M π)) ∧
      Tendsto (fun k => PandoraBO.expectedReward M (policies k)) atTop
        (nhds (PandoraBO.expectedReward M π)) := by
  exact PandoraBO.Private20261023.ZeroMultiplierPolicyLimit.zero_policy_limit_core M multipliers hpos hmono hlim
