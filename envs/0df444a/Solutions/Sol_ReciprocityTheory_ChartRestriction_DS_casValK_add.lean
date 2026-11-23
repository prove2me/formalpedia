-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casValK_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:46.890804+00:00
-- url     : https://prove2.me/submissions/2f4abee6-1596-4590-bf2c-ef05fbcc272c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section NumRho
variable {ε : Fin n → Bool}
private theorem nsq_add_bochner_inequality (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  simp only [nsq, dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring
end NumRho
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (μ ν : Fin n → ℝ) :
    casValK ε (μ + ν) = casValK ε μ + 2 * dot (μ + rhoC ε) ν + nsq ν := by
  simp only [casValK]
  rw [add_right_comm μ ν (rhoC ε), nsq_add_bochner_inequality]
  ring
end ReciprocityTheory.ChartRestriction.DS
