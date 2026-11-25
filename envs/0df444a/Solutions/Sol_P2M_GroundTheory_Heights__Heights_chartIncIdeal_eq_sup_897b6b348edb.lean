-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chartIncIdeal_eq_sup_897b6b348edb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:26:00.27641+00:00
-- url     : https://prove2.me/submissions/397c2ff0-c35f-443e-91a7-4f75e83acb66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : Type} [Field F] {n : ℕ} {I W : Ideal (MvPolynomial (Fin n) F)}
    (t : Fin n → F) (e : ℕ) (h : I ≤ W) :
    chartIncIdeal W t e = W.map (rename Sum.inl) ⊔ chartIncIdeal I t e := by
  unfold chartIncIdeal
  rw [Ideal.map_sup, Ideal.map_sup]
  have hba : I.map (rename (Sum.inl : Fin n → Fin n ⊕ Fin e × Fin n)) ≤
      W.map (rename (Sum.inl : Fin n → Fin n ⊕ Fin e × Fin n)) := Ideal.map_mono h
  apply le_antisymm
  · exact sup_le (sup_le le_sup_left (le_sup_of_le_right (le_sup_of_le_left le_sup_right)))
      (le_sup_of_le_right le_sup_right)
  · exact sup_le (le_sup_of_le_left le_sup_left)
      (sup_le (sup_le (le_sup_of_le_left (le_sup_of_le_left hba)) (le_sup_of_le_left le_sup_right))
        le_sup_right)
end GroundTheory.Heights₂.Heights
