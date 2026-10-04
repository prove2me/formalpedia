-- Prove2me | solution 1 for TimeChange.positive_time_change_flow
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T15:23:49.890094+00:00
-- url     : https://prove2.me/submissions/e8c62494-00f7-44a8-881c-4c4212c71d93

import Mathlib.Dynamics.Flow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring
import Theorems.Thm_TimeChange_complete_positive_clock
import Theorems.Thm_TimeChange_continuous_inverse_clock_family
open Set
open scoped Topology ContDiff
set_option maxHeartbeats 800000

theorem solution {S : Type*} [TopologicalSpace S]
    (flow : Flow ℝ S) (r : S → ℝ) (hr : Continuous r)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ s, m ≤ r s) :
    ∃ c : S → (ℝ ≃o ℝ), ∃ newFlow : Flow ℝ S,
      (∀ s, c s 0 = 0) ∧
      (∀ s t, HasDerivAt (c s) (r (flow t s)) t) ∧
      (∀ t s, newFlow t s = flow ((c s).symm t) s) ∧
      (∀ s a b, c s (a + b) = c s b + c (flow b s) a) ∧
      Continuous (fun p : ℝ × S => c p.2 p.1) := by
  classical
  have hex (s : S) := TimeChange.complete_positive_clock (fun t => r (flow t s))
    (hr.comp (flow.continuous continuous_id continuous_const)) m hm
    (fun t => hbound (flow t s))
  let c : S → (ℝ ≃o ℝ) := fun s => (hex s).choose
  have hz (s : S) : c s 0 = 0 := (hex s).choose_spec.1
  have hd (s : S) (t : ℝ) : HasDerivAt (c s) (r (flow t s)) t :=
    (hex s).choose_spec.2.1 t
  have hi (s : S) (t : ℝ) : c s t = ∫ v in (0 : ℝ)..t, r (flow v s) :=
    (hex s).choose_spec.2.2.2 t
  have hc : Continuous (fun p : ℝ × S => c p.2 p.1) := by
    have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := (0 : ℝ))
      (μ := MeasureTheory.volume)
      (f := fun p : ℝ × S => fun v : ℝ => r (flow v p.2))
      (hr.comp (flow.continuous continuous_snd (continuous_snd.comp continuous_fst)))
      continuous_fst
    convert h using 1
    funext p
    exact hi p.2 p.1
  have hinv := TimeChange.continuous_inverse_clock_family c hc
  have hcocycle (s : S) (a b : ℝ) : c s (a + b) = c s b + c (flow b s) a := by
    let g : ℝ → ℝ := fun v => c s (v + b) - c (flow b s) v
    have hg (v : ℝ) : HasDerivAt g 0 v := by
      have h := ((hd s (v + b)).comp v ((hasDerivAt_id v).add_const b)).sub
        (hd (flow b s) v)
      convert h using 1 <;> first | rfl | (simp only [flow.map_add, mul_one, sub_self])
    have heq := is_const_of_deriv_eq_zero (fun v => (hg v).differentiableAt)
      (fun v => (hg v).deriv) a 0
    dsimp [g] at heq
    rw [zero_add, hz] at heq
    linarith
  have hzInv (s : S) : (c s).symm 0 = 0 := by
    have h := (c s).symm_apply_apply 0
    rw [hz] at h
    exact h
  let newFlow : Flow ℝ S := {
    toFun := fun t s => flow ((c s).symm t) s
    cont' := flow.continuous hinv continuous_snd
    map_zero' := fun s => by simp only [hzInv, flow.map_zero, id_eq]
    map_add' := fun a b s => by
      have ht : (c s).symm (a + b) =
          (c (flow ((c s).symm b) s)).symm a + (c s).symm b := by
        apply (c s).injective
        rw [OrderIso.apply_symm_apply, hcocycle, OrderIso.apply_symm_apply,
          OrderIso.apply_symm_apply]
        exact add_comm a b
      rw [ht, flow.map_add]
  }
  exact ⟨c, newFlow, hz, hd, fun _ _ => rfl, hcocycle, hc⟩
