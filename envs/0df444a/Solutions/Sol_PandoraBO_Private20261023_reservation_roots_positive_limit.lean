-- Prove2me | solution 1 for PandoraBO.Private20261023.reservation_roots_positive_limit
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:16:15.117199+00:00
-- url     : https://prove2.me/submissions/b27485bb-f176-4551-8a99-a5f5090b2ba9

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_reservation_index_exists_unique
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace PandoraBO.Private20261023.ReservationPositiveLimit

theorem payoff_integrable {n : ℕ} (M : Instance n) (i : Box n) (z : ℝ) :
    Integrable (fun y : ℝ => max (y - z) 0) (M.law i) := by
  letI : IsProbabilityMeasure (M.law i) := M.law_probability i
  exact ((M.reward_integrable i).sub (integrable_const z)).pos_part

theorem improvement_antitone {n : ℕ} (M : Instance n) (i : Box n) :
    Antitone (expectedImprovement M i) := by
  intro z w hzw
  exact integral_mono (payoff_integrable M i w) (payoff_integrable M i z)
    (fun y => max_le_max (sub_le_sub_left hzw y) le_rfl)

theorem roots_tendsto {n : ℕ} (M : Instance n) (i : Box n)
    (multipliers roots : ℕ → ℝ) (limit root : ℝ)
    (hlim : Tendsto multipliers atTop (nhds limit))
    (hroots : ∀ k, reservationRoot M i (multipliers k * M.cost i) (roots k))
    (hroot : reservationRoot M i (limit * M.cost i) root)
    (hunique : ∀ w : ℝ, reservationRoot M i (limit * M.cost i) w → w = root) :
    Tendsto roots atTop (nhds root) := by
  have hcostlim : Tendsto (fun k => multipliers k * M.cost i) atTop
      (nhds (limit * M.cost i)) := hlim.mul_const (M.cost i)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hweak : limit * M.cost i ≤ expectedImprovement M i a := by
      have h := improvement_antitone M i ha.le
      rw [hroot] at h
      exact h
    have hstrict : limit * M.cost i < expectedImprovement M i a := by
      refine lt_of_le_of_ne hweak ?_
      intro heq
      have ha_eq : a = root := hunique a heq.symm
      exact (ne_of_lt ha) ha_eq
    have hsmall : ∀ᶠ k in atTop,
        multipliers k * M.cost i < expectedImprovement M i a :=
      hcostlim.eventually_lt tendsto_const_nhds hstrict
    filter_upwards [hsmall] with k hk
    apply lt_of_not_ge
    intro hle
    have h := improvement_antitone M i hle
    rw [hroots k] at h
    exact not_le_of_gt hk h
  · intro b hb
    have hweak : expectedImprovement M i b ≤ limit * M.cost i := by
      have h := improvement_antitone M i hb.le
      rw [hroot] at h
      exact h
    have hstrict : expectedImprovement M i b < limit * M.cost i := by
      refine lt_of_le_of_ne hweak ?_
      intro heq
      have hb_eq : b = root := hunique b heq
      exact (ne_of_gt hb) hb_eq
    have hlarge : ∀ᶠ k in atTop,
        expectedImprovement M i b < multipliers k * M.cost i :=
      tendsto_const_nhds.eventually_lt hcostlim hstrict
    filter_upwards [hlarge] with k hk
    apply lt_of_not_ge
    intro hle
    have h := improvement_antitone M i hle
    rw [hroots k] at h
    exact not_le_of_gt hk h

end PandoraBO.Private20261023.ReservationPositiveLimit

theorem solution {n : ℕ} (M : PandoraBO.Instance n) (i : PandoraBO.Box n)
    (multipliers : ℕ → ℝ) (limit : ℝ)
    (hpos : ∀ k, 0 < multipliers k) (hlimitpos : 0 < limit)
    (hlim : Tendsto multipliers atTop (nhds limit)) :
    ∃ roots : ℕ → ℝ, ∃ root : ℝ,
      (∀ k, PandoraBO.reservationRoot M i (multipliers k * M.cost i) (roots k)) ∧
      PandoraBO.reservationRoot M i (limit * M.cost i) root ∧
      Tendsto roots atTop (nhds root) := by
  classical
  have hexists : ∀ k, ∃ z : ℝ,
      PandoraBO.reservationRoot M i (multipliers k * M.cost i) z := fun k =>
    (PandoraBO.Private20261023.reservation_index_exists_unique M (multipliers k) (hpos k) i).exists
  let roots : ℕ → ℝ := fun k => Classical.choose (hexists k)
  have hroots : ∀ k, PandoraBO.reservationRoot M i (multipliers k * M.cost i) (roots k) :=
    fun k => Classical.choose_spec (hexists k)
  obtain ⟨root, hroot, hunique⟩ :=
    PandoraBO.Private20261023.reservation_index_exists_unique M limit hlimitpos i
  exact ⟨roots, root, hroots, hroot,
    PandoraBO.Private20261023.ReservationPositiveLimit.roots_tendsto M i
      multipliers roots limit root hlim hroots hroot hunique⟩
