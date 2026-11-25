-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.cextL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:46.644899+00:00
-- url     : https://prove2.me/submissions/73fe84a6-7cc9-4a11-9c04-87f732fe747f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelCext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hA : RLinOnK ε A)
    (Z : Matrix (Fin n) (Fin n) ℂ) : cextL ε A hA Z = cext ε A Z := rfl
end ReciprocityTheory.ChartRestriction.DS.HW
