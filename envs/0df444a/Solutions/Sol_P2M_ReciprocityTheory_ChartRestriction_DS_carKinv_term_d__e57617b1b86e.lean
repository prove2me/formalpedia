-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_term_d__e57617b1b86e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:49:57.132841+00:00
-- url     : https://prove2.me/submissions/c130b57f-65bd-45e0-90a2-83a571d17ae1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARKinv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carKinv_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carKinv_E_sgE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b i c : Fin n) :
    E i c * cm i c * diagE ε E cp cm a b - diagE ε E cp cm a b * (E i c * cm i c) =
      ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
        E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) := by
  unfold diagE
  rw [carKinv_expand _ _ _ _ (hEC a b i c).2.symm (carKinv_E_sgE hEC ε a b i c), hE i c a b]
end ReciprocityTheory.ChartRestriction.DS
