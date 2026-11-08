-- Prove2me | solution 1 for OmniMix.closed_forms_bv_dv
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:45:59.017335+00:00
-- url     : https://prove2.me/submissions/e228ceda-3251-4ba6-bf4b-8025ebfe83da

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_vLoss
import Definitions.Def_OmniMix_bTest
import Definitions.Def_OmniMix_dGain
import Definitions.Def_OmniMix_bV
import Definitions.Def_OmniMix_dV

namespace Aux_OmniMix_cf
open OmniMix

theorem bern_coe (p : unitInterval) (g : Bool → ℝ) :
    bern p (fun y => ((g y : ℝ) : EReal)) = (((1 - (p : ℝ)) * g false + (p : ℝ) * g true : ℝ) : EReal) := by
  unfold bern
  rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]

theorem E_le (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (p q : unitInterval) :
    (1 - (p : ℝ)) * vLossR v p false + (p : ℝ) * vLossR v p true ≤
      (1 - (p : ℝ)) * vLossR v q false + (p : ℝ) * vLossR v q true := by
  have hp0 := p.2.1
  have hp1 := p.2.2
  unfold vLossR
  simp only [Bool.false_eq_true, if_false, if_true]
  split_ifs <;> nlinarith

end Aux_OmniMix_cf

open OmniMix Aux_OmniMix_cf in
theorem solution (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    IsProper (vLoss v) ∧ ∀ p q : unitInterval,
      bTest (vLoss v) p q = ((bV v p q : ℝ) : EReal) ∧
        dGain (vLoss v) p q = ((dV v p q : ℝ) : EReal) := by
  refine ⟨fun p q => ?_, fun p q => ⟨?_, ?_⟩⟩
  · show bern p (fun y => ((vLossR v p y : ℝ) : EReal)) ≤ bern p (fun y => ((vLossR v q y : ℝ) : EReal))
    rw [bern_coe, bern_coe, EReal.coe_le_coe_iff]
    exact E_le v hv0 hv1 p q
  · have hp0 := p.2.1
    have hp1 := p.2.2
    unfold bTest lossDiff vLoss
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
    unfold vLossR bV
    simp only [Bool.false_eq_true, if_false, if_true]
    rcases lt_or_ge (p : ℝ) v with hp | hp <;> rcases lt_or_ge (q : ℝ) v with hq | hq
    · simp only [hp, hq, not_le.mpr hp, not_le.mpr hq, if_true, if_false, and_false, false_and]; ring
    · simp only [hp, not_lt.mpr hq, not_le.mpr hp, hq, if_true, if_false, and_true, true_and,
        false_and, and_false]; ring
    · simp only [not_lt.mpr hp, hp, hq, not_le.mpr hq, if_true, if_false, and_true, true_and,
        false_and, and_false]; ring
    · simp only [not_lt.mpr hp, hp, not_lt.mpr hq, hq, if_true, if_false, and_true, true_and,
        false_and, and_false]; ring
  · unfold dGain vLoss
    have : (fun y => ((vLossR v q y : ℝ) : EReal) - ((vLossR v p y : ℝ) : EReal)) =
        fun y => ((vLossR v q y - vLossR v p y : ℝ) : EReal) := by
      funext y; rw [EReal.coe_sub]
    rw [this, bern_coe, EReal.coe_eq_coe_iff]
    have hp0 := p.2.1
    have hp1 := p.2.2
    unfold vLossR dV bV
    simp only [Bool.false_eq_true, if_false, if_true]
    rcases lt_or_ge (p : ℝ) v with hp | hp <;> rcases lt_or_ge (q : ℝ) v with hq | hq
    · simp only [hp, hq, not_le.mpr hp, not_le.mpr hq, if_true, if_false, and_false, false_and]; ring
    · simp only [hp, not_lt.mpr hq, not_le.mpr hp, hq, if_true, if_false, and_true, true_and,
        false_and, and_false]
      rw [abs_of_nonneg (by linarith)]; ring
    · simp only [not_lt.mpr hp, hp, hq, not_le.mpr hq, if_true, if_false, and_true, true_and,
        false_and, and_false]
      rw [abs_of_nonpos (by linarith)]; ring
    · simp only [not_lt.mpr hp, hp, not_lt.mpr hq, hq, if_true, if_false, and_true, true_and,
        false_and, and_false]; ring
