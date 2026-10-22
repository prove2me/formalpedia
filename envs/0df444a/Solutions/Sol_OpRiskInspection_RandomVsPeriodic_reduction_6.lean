-- Prove2me | solution 1 for OpRiskInspection.RandomVsPeriodic.reduction_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:10:55.359376+00:00
-- url     : https://prove2.me/submissions/c84e77aa-b157-4391-9b17-2c8bad86b566

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting
set_option autoImplicit false
open OpRiskInspection.RandomVsPeriodic

theorem solution (p : Params) (hp : Standing p) (K v P w : ℝ)
    (F : MeasureTheory.Measure ℝ) (a : Effort)
    (hv : 0 < v) (hK : 0 < K) (ha : AgentOptimal p F P a)
    (hbind : agentPayoff p F a P w = p.pibar) :
    principalPayoff p K v F a P w = reducedPayoff p K v F a := by
  have hr : p.r ≠ 0 := hp.hr.ne'
  unfold agentPayoff at hbind
  unfold principalPayoff reducedPayoff mubar
  have h1 : (p.mu - p.r * p.pibar) / p.r = p.mu / p.r - p.pibar := by field_simp
  have h2 : (p.mu - w) / p.r = p.mu / p.r - w / p.r := sub_div _ _ _
  rw [h1, h2]
  linarith
