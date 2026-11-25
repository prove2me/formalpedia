-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalSheets_homogenize_ne_zero_b4aa12b26ec4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:22.706083+00:00
-- url     : https://prove2.me/submissions/c14409eb-3ef4-4df7-9241-1b89eb8c03d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eval_homogenize_d7a73378accb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
open Matrix
open GroundTheory.Heights₂.Heights.ConeLocalSheets
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ConeLocalSheets
theorem _root_.solution {c : MvPolynomial (Fin e) ℂ} (hc : c ≠ 0) : homogenize c ≠ 0 := by
  intro h
  apply hc
  apply MvPolynomial.funext
  intro x
  have := congrArg (eval (Fin.cons 1 x : Fin (e + 1) → ℂ)) h
  rw [eval_homogenize, map_zero] at this
  simpa using this
end GroundTheory.Heights₂.Heights.ConeLocalSheets
