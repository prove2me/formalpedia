-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_weight_groupWeight_5a5488b15ad2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:44:50.518524+00:00
-- url     : https://prove2.me/submissions/a035bb4f-de4c-495e-ac04-40f43df1691f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm

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
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {k : ℕ} (m : Fin k × Fin n →₀ ℕ) :
    Finsupp.weight (groupWeight k n) m = fun i => ∑ j, m (i, j) := by
  funext i
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intros; exact zero_smul _ _), Finset.sum_apply,
    Fintype.sum_prod_type]
  simp [groupWeight, Pi.single_apply]
end GroundTheory.Heights₂.Heights.ObjectsChow
