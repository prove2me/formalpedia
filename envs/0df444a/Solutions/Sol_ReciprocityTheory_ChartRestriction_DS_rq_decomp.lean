-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rq_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:52.945732+00:00
-- url     : https://prove2.me/submissions/fff54f3c-4176-4261-903c-51ef05af8469

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    (1 / 2 : ℂ) • (X - Jm ε * Xᴴ * Jm ε) + (-(Complex.I / 2)) • (Complex.I • (X + Jm ε * Xᴴ * Jm ε))
      = X := by
  have h : -(Complex.I / 2) * Complex.I = 1 / 2 := by
    rw [neg_mul, div_mul_eq_mul_div, Complex.I_mul_I]
    ring
  rw [smul_smul, h, ← smul_add, sub_add_add_cancel, ← two_smul ℂ X, smul_smul]
  norm_num
end ReciprocityTheory.ChartRestriction.DS
