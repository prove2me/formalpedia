-- Prove2me | solution 1 for actuarial_c_cont_annual_settlement_discount_order
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:54:10.515013+00:00
-- url     : https://prove2.me/submissions/2de06b04-a648-4d5a-9a73-bc251f515ab9

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_annualSettlementPV

open ActuarialAssurances.Continuous

open MeasureTheory


theorem solution (h : ℕ) (delta t : ℝ)
    (hdelta : 0 ≤ delta) (ht : 0 ≤ t) (horizon : t < (h : ℝ)) :
    annualSettlementPV h delta t ≤ deathPV (h : ℝ) delta t := by
  have hd : deathPV (h : ℝ) delta t = Real.exp (-delta * t) := by simp [deathPV, ht, horizon]
  rw [hd]; unfold annualSettlementPV
  rw [Finset.sum_eq_single ⌊t⌋₊]
  · split_ifs with hc
    · apply Real.exp_le_exp.mpr
      have := hc.2
      push_cast at this ⊢
      nlinarith
    · exact (Real.exp_pos _).le
  · intro j _ hj
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hj
    push_cast at h2
    exact ((Nat.floor_eq_iff ht).mpr ⟨h1, h2⟩).symm
  · intro hn; exfalso; apply hn
    rw [Finset.mem_range]
    exact (Nat.floor_lt ht).mpr horizon

