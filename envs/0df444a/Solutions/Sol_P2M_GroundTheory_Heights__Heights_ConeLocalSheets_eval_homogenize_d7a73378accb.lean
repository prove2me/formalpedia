-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eval_homogenize_d7a73378accb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:21.425615+00:00
-- url     : https://prove2.me/submissions/3f4a21c1-a6c0-459c-bb1c-ba01172526be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets

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
theorem _root_.solution (c : MvPolynomial (Fin e) ℂ) (x : Fin e → ℂ) :
    eval (Fin.cons 1 x : Fin (e + 1) → ℂ) (homogenize c) = eval x c := by
  have hcs : (Fin.cons 1 x : Fin (e + 1) → ℂ) ∘ Fin.succ = x := funext fun i => Fin.cons_succ _ _ _
  conv_rhs => rw [c.as_sum]
  simp only [homogenize, map_sum, map_mul, eval_C, map_pow, eval_X, Fin.cons_zero, one_pow, one_mul,
    eval_rename, hcs, eval_monomial]
end GroundTheory.Heights₂.Heights.ConeLocalSheets
