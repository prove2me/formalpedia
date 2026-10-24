-- Prove2me | solution 1 for PandoraBO.Private20261023.monotone_multiplier_optimal_policy_limit
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:29:44.966814+00:00
-- url     : https://prove2.me/submissions/fa85f163-05e1-46c0-a332-7ceeff75603f

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_reservation_index_exists_unique
import Theorems.Thm_PandoraBO_Private20261023_reservation_roots_positive_limit
import Theorems.Thm_PandoraBO_Private20261023_reservation_roots_strict_antitone
import Theorems.Thm_PandoraBO_Private20261023_finite_index_policy_subsequence_limit
import Theorems.Thm_PandoraBO_Private20261023_optimal_policy_subsequence_limits
import Theorems.Thm_PandoraBO_Private20261023_monotone_multiplier_limit_dichotomy
import Theorems.Thm_PandoraBO_Private20261023_weitzman_optimality
import Mathlib.Topology.Instances.EReal.Lemmas

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace PandoraBO.Private20261023.PositiveMultiplierPolicyLimit

theorem from_one_side {n : ℕ} (M : Instance n)
    (multipliers : ℕ → ℝ) (limit : ℝ)
    (hpos : ∀ k, 0 < multipliers k) (hlimitpos : 0 < limit)
    (hmono : Monotone multipliers ∨ Antitone multipliers)
    (roots : Box n → ℕ → ℝ) (root : Box n → ℝ)
    (hroots : ∀ i k, reservationRoot M i (multipliers k * M.cost i) (roots i k))
    (hroot : reservationIndices M limit root)
    (hrootslim : ∀ i, Tendsto (roots i) atTop (nhds (root i)))
    (weak : Bool)
    (hside : ∀ i k, if weak then (root i : EReal) < (roots i k : EReal)
      else (roots i k : EReal) ≤ (root i : EReal)) :
    ∃ policies : ℕ → Policy n, ∃ π : Policy n,
      (∀ k, isGittinsPolicy M (multipliers k) (policies k)) ∧
      isGittinsPolicy M limit π ∧
      Tendsto (fun k => expectedCost M (policies k)) atTop (nhds (expectedCost M π)) ∧
      Tendsto (fun k => expectedReward M (policies k)) atTop (nhds (expectedReward M π)) := by
  classical
  let zs : ℕ → Box n → EReal := fun k i => (roots i k : EReal)
  let z : Box n → EReal := fun i => (root i : EReal)
  have hzlim : ∀ i, Tendsto (fun k => zs k i) atTop (nhds (z i)) :=
    fun i => EReal.tendsto_coe.mpr (hrootslim i)
  obtain ⟨policies, hsameindex, hpolicies, extraction, π, hextract, hπ, hcost, hreward⟩ :=
    finite_index_policy_subsequence_limit M zs z weak hzlim hside
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
  have hlimitgittins : isGittinsPolicy M limit π := by
    refine ⟨root, hroot, ?_, ?_⟩
    · simpa only [z, EReal.coe_le_coe_iff] using hπ.1
    · intro h u hh
      have hi := hπ.2 h u hh
      cases hnext : π.next (h,u) with
      | none =>
          simp only [hnext] at hi ⊢
          simpa only [z, EReal.coe_le_coe_iff] using hi
      | some i =>
          simp only [hnext] at hi ⊢
          simpa only [z, EReal.coe_le_coe_iff] using hi
  have hlimits := optimal_policy_subsequence_limits M multipliers (fun k => (hpos k).le)
    policies (fun k => (weitzman_optimality M (multipliers k) (hpos k)).2 _ (hgittins k))
    hsame hmono extraction hextract (expectedCost M π) (expectedReward M π) hcost hreward
  exact ⟨policies, π, hgittins, hlimitgittins, hlimits.1, hlimits.2⟩

theorem from_eventually_constant {n : ℕ} (M : Instance n)
    (multipliers : ℕ → ℝ) (limit : ℝ)
    (hpos : ∀ k, 0 < multipliers k) (hlimitpos : 0 < limit)
    (K : ℕ) (hconstant : ∀ k, K ≤ k → multipliers k = limit) :
    ∃ policies : ℕ → Policy n, ∃ π : Policy n,
      (∀ k, isGittinsPolicy M (multipliers k) (policies k)) ∧
      isGittinsPolicy M limit π ∧
      Tendsto (fun k => expectedCost M (policies k)) atTop (nhds (expectedCost M π)) ∧
      Tendsto (fun k => expectedReward M (policies k)) atTop (nhds (expectedReward M π)) := by
  classical
  obtain ⟨π, hπ⟩ := (weitzman_optimality M limit hlimitpos).1
  have hchoice : ∀ k, ∃ πk : Policy n, isGittinsPolicy M (multipliers k) πk :=
    fun k => (weitzman_optimality M (multipliers k) (hpos k)).1
  choose selected hselected using hchoice
  let policies : ℕ → Policy n := fun k => if multipliers k = limit then π else selected k
  have hpolicies : ∀ k, isGittinsPolicy M (multipliers k) (policies k) := by
    intro k
    by_cases hk : multipliers k = limit
    · simpa only [policies, if_pos hk, hk] using hπ
    · simpa only [policies, if_neg hk] using hselected k
  have hevent : ∀ᶠ k in atTop, policies k = π :=
    (eventually_ge_atTop K).mono (fun k hk => by simp only [policies, if_pos (hconstant k hk)])
  refine ⟨policies, π, hpolicies, hπ, ?_, ?_⟩
  · exact Filter.Tendsto.congr'
      (hevent.mono (fun k hk => (congrArg (expectedCost M) hk).symm)) tendsto_const_nhds
  · exact Filter.Tendsto.congr'
      (hevent.mono (fun k hk => (congrArg (expectedReward M) hk).symm)) tendsto_const_nhds

end PandoraBO.Private20261023.PositiveMultiplierPolicyLimit

theorem solution {n : ℕ} (M : PandoraBO.Instance n)
    (multipliers : ℕ → ℝ) (limit : ℝ)
    (hpos : ∀ k, 0 < multipliers k) (hlimitpos : 0 < limit)
    (hmono : Monotone multipliers ∨ Antitone multipliers)
    (hlim : Tendsto multipliers atTop (nhds limit)) :
    ∃ policies : ℕ → PandoraBO.Policy n, ∃ π : PandoraBO.Policy n,
      (∀ k, PandoraBO.isGittinsPolicy M (multipliers k) (policies k)) ∧
      PandoraBO.isGittinsPolicy M limit π ∧
      Tendsto (fun k => PandoraBO.expectedCost M (policies k)) atTop
        (nhds (PandoraBO.expectedCost M π)) ∧
      Tendsto (fun k => PandoraBO.expectedReward M (policies k)) atTop
        (nhds (PandoraBO.expectedReward M π)) := by
  classical
  have hchoice := fun i : PandoraBO.Box n =>
    PandoraBO.Private20261023.reservation_roots_positive_limit M i multipliers limit
      hpos hlimitpos hlim
  choose roots root hroots hroot hrootslim using hchoice
  rcases PandoraBO.Private20261023.monotone_multiplier_limit_dichotomy
    multipliers limit hmono hlim with ⟨hinc, hbelow⟩ | ⟨hdec, habove⟩ | ⟨K, hconstant⟩
  · apply PandoraBO.Private20261023.PositiveMultiplierPolicyLimit.from_one_side M
      multipliers limit hpos hlimitpos (Or.inl hinc) roots root hroots hroot hrootslim true
    intro i k
    exact EReal.coe_lt_coe_iff.mpr
      (PandoraBO.Private20261023.reservation_roots_strict_antitone M i
        (multipliers k) limit (roots i k) (root i) (hbelow k) (hroots i k) (hroot i))
  · apply PandoraBO.Private20261023.PositiveMultiplierPolicyLimit.from_one_side M
      multipliers limit hpos hlimitpos (Or.inr hdec) roots root hroots hroot hrootslim false
    intro i k
    exact EReal.coe_le_coe_iff.mpr
      (PandoraBO.Private20261023.reservation_roots_strict_antitone M i
        limit (multipliers k) (root i) (roots i k) (habove k) (hroot i) (hroots i k)).le
  · exact PandoraBO.Private20261023.PositiveMultiplierPolicyLimit.from_eventually_constant M
      multipliers limit hpos hlimitpos K hconstant
