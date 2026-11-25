-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.ccb_cpart_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:20.494868+00:00
-- url     : https://prove2.me/submissions/3ac857c7-8096-47bb-94e4-7c95b4f0f5cb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainB

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε Z + Complex.I • cpart2 ε Z = Z := by
  unfold cpart1 cpart2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add,
    show (Z - Jm ε * Zᴴ * Jm ε) + (Z + Jm ε * Zᴴ * Jm ε) = (2 : ℂ) • Z by rw [two_smul]; abel,
    smul_smul]
  norm_num
end ReciprocityTheory.ChartRestriction.DS.S7
