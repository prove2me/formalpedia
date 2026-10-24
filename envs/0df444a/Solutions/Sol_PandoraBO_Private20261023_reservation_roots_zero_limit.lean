-- Prove2me | solution 1 for PandoraBO.Private20261023.reservation_roots_zero_limit
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:07:24.814505+00:00
-- url     : https://prove2.me/submissions/1fe79550-49b2-408f-b76f-344219dcb9c7

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_reservation_index_exists_unique
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Topology.Instances.EReal.Lemmas

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace PandoraBO.Private20261023.ReservationZeroLimit

theorem payoff_integrable {n : ℕ} (M : Instance n) (i : Box n) (z : ℝ) :
    Integrable (fun y : ℝ => max (y - z) 0) (M.law i) := by
  letI : IsProbabilityMeasure (M.law i) := M.law_probability i
  exact ((M.reward_integrable i).sub (integrable_const z)).pos_part

theorem improvement_nonneg {n : ℕ} (M : Instance n) (i : Box n) (z : ℝ) :
    0 ≤ expectedImprovement M i z :=
  integral_nonneg (fun y => le_max_right (y - z) 0)

theorem improvement_antitone {n : ℕ} (M : Instance n) (i : Box n) :
    Antitone (expectedImprovement M i) := by
  intro z w hzw
  exact integral_mono (payoff_integrable M i w) (payoff_integrable M i z)
    (fun y => max_le_max (sub_le_sub_left hzw y) le_rfl)

theorem improvement_zero_iff {n : ℕ} (M : Instance n) (i : Box n) (z : ℝ) :
    expectedImprovement M i z = 0 ↔ ∀ᵐ y ∂M.law i, y ≤ z := by
  have hint := integral_eq_zero_iff_of_nonneg
    (fun y : ℝ => le_max_right (y - z) 0) (payoff_integrable M i z)
  change (∫ y : ℝ, max (y - z) 0 ∂M.law i) = 0 ↔ _
  rw [hint]
  constructor
  · intro h
    filter_upwards [h] with y hy
    have hle : y - z ≤ 0 := (le_max_left (y - z) 0).trans_eq hy
    exact sub_nonpos.mp hle
  · intro h
    filter_upwards [h] with y hy
    exact max_eq_right (sub_nonpos.mpr hy)

theorem zeroIndex_eq_essSup {n : ℕ} (M : Instance n) (i : Box n) :
    zeroReservationIndex M i = essSup (fun y : ℝ => (y : EReal)) (M.law i) := by
  rfl

theorem zeroIndex_le_iff {n : ℕ} (M : Instance n) (i : Box n) (z : ℝ) :
    zeroReservationIndex M i ≤ (z : EReal) ↔ ∀ᵐ y ∂M.law i, y ≤ z := by
  constructor
  · intro hz
    have hae : ∀ᵐ (y : ℝ) ∂M.law i, (y : EReal) ≤ zeroReservationIndex M i := by
      rw [zeroIndex_eq_essSup]
      exact ae_le_essSup (f := fun y : ℝ => (y : EReal)) (μ := M.law i)
    filter_upwards [hae] with y hy
    exact EReal.coe_le_coe_iff.mp (hy.trans hz)
  · intro hz
    apply sInf_le
    exact hz.mono (fun y hy => EReal.coe_le_coe_iff.mpr hy)

theorem improvement_pos_iff {n : ℕ} (M : Instance n) (i : Box n) (z : ℝ) :
    0 < expectedImprovement M i z ↔ (z : EReal) < zeroReservationIndex M i := by
  constructor
  · intro hpos
    apply lt_of_not_ge
    intro hz
    exact hpos.ne' ((improvement_zero_iff M i z).mpr ((zeroIndex_le_iff M i z).mp hz))
  · intro hz
    have hne : expectedImprovement M i z ≠ 0 := by
      intro hzero
      have hupper := (zeroIndex_le_iff M i z).mpr ((improvement_zero_iff M i z).mp hzero)
      exact not_le_of_gt hz hupper
    exact lt_of_le_of_ne (improvement_nonneg M i z) hne.symm

/-- No monotonicity of the multipliers is needed for convergence of one index. -/
theorem roots_tendsto_zeroIndex {n : ℕ} (M : Instance n) (i : Box n)
    (multipliers roots : ℕ → ℝ)
    (hpos : ∀ k, 0 < multipliers k)
    (hlim : Tendsto multipliers atTop (nhds 0))
    (hroots : ∀ k, reservationRoot M i (multipliers k * M.cost i) (roots k)) :
    Tendsto (fun k => (roots k : EReal)) atTop (nhds (zeroReservationIndex M i)) := by
  have hrootpos (k : ℕ) : 0 < expectedImprovement M i (roots k) := by
    rw [hroots k]
    exact mul_pos (hpos k) (M.cost_positive i)
  have hbelow (k : ℕ) : (roots k : EReal) < zeroReservationIndex M i :=
    (improvement_pos_iff M i (roots k)).mp (hrootpos k)
  have hcostlim : Tendsto (fun k => multipliers k * M.cost i) atTop (nhds 0) := by
    simpa only [zero_mul] using hlim.mul_const (M.cost i)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r, har, hrindex⟩ := EReal.exists_rat_btwn_of_lt ha
    have hrpos : 0 < expectedImprovement M i (r : ℝ) :=
      (improvement_pos_iff M i (r : ℝ)).mpr hrindex
    have hsmall : ∀ᶠ k in atTop, multipliers k * M.cost i < expectedImprovement M i (r : ℝ) :=
      hcostlim.eventually_lt tendsto_const_nhds hrpos
    filter_upwards [hsmall] with k hk
    have hrroot : (r : ℝ) < roots k := by
      apply lt_of_not_ge
      intro hle
      have hEI := improvement_antitone M i hle
      rw [hroots k] at hEI
      exact not_le_of_gt hk hEI
    exact har.trans (EReal.coe_lt_coe_iff.mpr hrroot)
  · intro b hb
    exact Filter.Eventually.of_forall (fun k => (hbelow k).trans hb)

end PandoraBO.Private20261023.ReservationZeroLimit

theorem solution {n : ℕ} (M : PandoraBO.Instance n) (i : PandoraBO.Box n) :
    (∀ z : ℝ, PandoraBO.expectedImprovement M i z = 0 ↔ ∀ᵐ y ∂M.law i, y ≤ z) ∧
    (∀ z : ℝ, 0 < PandoraBO.expectedImprovement M i z ↔
      (z : EReal) < PandoraBO.zeroReservationIndex M i) ∧
    ∀ multipliers : ℕ → ℝ, (∀ k, 0 < multipliers k) →
      Tendsto multipliers atTop (nhds 0) → ∃ roots : ℕ → ℝ,
        (∀ k, PandoraBO.reservationRoot M i (multipliers k * M.cost i) (roots k)) ∧
        Tendsto (fun k => (roots k : EReal)) atTop (nhds (PandoraBO.zeroReservationIndex M i)) := by
  classical
  refine ⟨PandoraBO.Private20261023.ReservationZeroLimit.improvement_zero_iff M i,
    PandoraBO.Private20261023.ReservationZeroLimit.improvement_pos_iff M i, ?_⟩
  intro multipliers hpos hlim
  have hexists : ∀ k, ∃ z : ℝ,
      PandoraBO.reservationRoot M i (multipliers k * M.cost i) z := fun k =>
    (PandoraBO.Private20261023.reservation_index_exists_unique M (multipliers k) (hpos k) i).exists
  let roots : ℕ → ℝ := fun k => Classical.choose (hexists k)
  have hroots : ∀ k, PandoraBO.reservationRoot M i (multipliers k * M.cost i) (roots k) :=
    fun k => Classical.choose_spec (hexists k)
  exact ⟨roots, hroots,
    PandoraBO.Private20261023.ReservationZeroLimit.roots_tendsto_zeroIndex M i
      multipliers roots hpos hlim hroots⟩
