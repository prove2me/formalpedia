-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.cf_mul_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:04.922824+00:00
-- url     : https://prove2.me/submissions/553f061e-0356-466b-a898-2f3d162800d1

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution {α β γ : Type*} [Fintype β] (P : Matrix α β ℂ[X]) (Q : Matrix β γ ℂ[X]) :
    cf 0 (P * Q) = cf 0 P * cf 0 Q := by
  rw [cf_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]
end ReciprocityTheory.AnForm.P
