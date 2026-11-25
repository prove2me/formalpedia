-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.carKinv_term_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:39.004874+00:00
-- url     : https://prove2.me/submissions/e110ce3d-c981-46c4-b1ce-fb38a020489a

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
    E c i * cp i c * diagE ε E cp cm a b - diagE ε E cp cm a b * (E c i * cp i c) =
      ((if i = a then E c b else 0) - (if b = c then E a i else 0)) * cp i c -
        E c i * (sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b) := by
  unfold diagE
  rw [carKinv_expand _ _ _ _ (hEC a b i c).1.symm (carKinv_E_sgE hEC ε a b c i), hE c i a b]
end ReciprocityTheory.ChartRestriction.DS
