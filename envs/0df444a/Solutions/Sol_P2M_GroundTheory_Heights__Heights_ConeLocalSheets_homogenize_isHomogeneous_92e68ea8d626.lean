-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalSheets_homogenize_isHomogeneous_92e68ea8d626
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:08:09.896681+00:00
-- url     : https://prove2.me/submissions/1b99bcb5-faae-456c-bc3b-fadf372e383b

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
theorem _root_.solution (c : MvPolynomial (Fin e) ℂ) :
    (homogenize c).IsHomogeneous c.totalDegree := by
  refine IsHomogeneous.sum _ _ _ fun m hm => ?_
  have hle : m.degree ≤ c.totalDegree := le_totalDegree hm
  have h := (isHomogeneous_X_pow (R := ℂ) (0 : Fin (e + 1)) (c.totalDegree - m.degree)).mul
    ((isHomogeneous_monomial (σ := Fin e) (R := ℂ) (d := m) 1 rfl).rename_isHomogeneous (f := Fin.succ))
  rw [Nat.sub_add_cancel hle] at h
  exact h.C_mul _
end GroundTheory.Heights₂.Heights.ConeLocalSheets
