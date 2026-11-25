-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIncOrd_equiv_apply_ca034950f9d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:35:59.407344+00:00
-- url     : https://prove2.me/submissions/b4720c05-c484-46b8-a867-cef685a33b56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncOrd

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
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIncOrd
variable {F : Type} [Field F] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
namespace GroundTheory.Heights₂.Heights.ChartIncOrd
theorem _root_.solution (y : MvPolynomial (Fin e × Fin n) (ChartQ I t)) : equiv I t e y = fwd I t e y := rfl
end GroundTheory.Heights₂.Heights.ChartIncOrd
