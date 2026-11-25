-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIncOrd_map_equiv_8568df807ce0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:36:18.207886+00:00
-- url     : https://prove2.me/submissions/c5f2555e-53d1-498a-99a0-f04400ad2934

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
theorem _root_.solution (W : Ideal (MvPolynomial (Fin n) F)) :
    ((W.map (mkQ I t)).map (C : ChartQ I t →+* MvPolynomial (Fin e × Fin n) (ChartQ I t))).map
        (equiv I t e : MvPolynomial (Fin e × Fin n) (ChartQ I t) →+* MvPolynomial (Fin e) (ChartInc I t e)) =
      (W.map (chartX I t e)).map (C : ChartInc I t e →+* MvPolynomial (Fin e) (ChartInc I t e)) := by
  have h1 : (equiv I t e : MvPolynomial (Fin e × Fin n) (ChartQ I t) →+* MvPolynomial (Fin e) (ChartInc I t e)).comp
      C = C.comp (toInc I t e) := RingHom.ext fun q => fwd_C I t e q
  have h2 : (toInc I t e).comp (mkQ I t) = chartX I t e := RingHom.ext fun _ => rfl
  rw [Ideal.map_map, h1, ← Ideal.map_map, Ideal.map_map (mkQ I t), h2]
end GroundTheory.Heights₂.Heights.ChartIncOrd
