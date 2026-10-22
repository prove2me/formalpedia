-- Prove2me | solution 1 for RobustPoA.Repeated.relation_23
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:10:29.149371+00:00
-- url     : https://prove2.me/submissions/91072f75-b9d5-4233-984f-fcc60837021f

import Mathlib
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Repeated_Regret

set_option autoImplicit false

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ)
    (hsm : RobustPoA.Static.IsSmooth C lam mu) (hmu : mu < 1) (s s' : ∀ i, S i) :
    RobustPoA.Static.cost C s ≤ lam / (1 - mu) * RobustPoA.Static.cost C s' +
      (∑ i, RobustPoA.Repeated.delta C s' s i) / (1 - mu) := by
  have h := hsm s s'
  have hd : ∑ i, RobustPoA.Repeated.delta C s' s i =
      RobustPoA.Static.cost C s - ∑ i, C i (Function.update s i (s' i)) := by
    unfold RobustPoA.Repeated.delta RobustPoA.Static.cost
    rw [Finset.sum_sub_distrib]
  have hpos : 0 < 1 - mu := by linarith
  rw [hd, div_mul_eq_mul_div, ← add_div, le_div_iff₀ hpos]
  nlinarith [h]
