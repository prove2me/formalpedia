-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_chartSubst_inr_48e68431394d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:46.056978+00:00
-- url     : https://prove2.me/submissions/7ef1cfa5-f2cf-445f-a7f0-f94fda3ba6a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_eval__genSubst_eq_map_1ab8fb3a62a0

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
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}
variable (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution (g : MvPolynomial (Fin e × Fin n) F) :
    chartSubst I t e (rename Sum.inr g) =
      map (chartX I t e) (aeval (genSubst (fun m => (X m : MvPolynomial (Fin n) F)) (fun m => C (t m))) g) := by
  rw [← eval₂_genSubst_eq_map, chartSubst, coe_eval₂Hom, eval₂_rename, Sum.elim_comp_inr]
end GroundTheory.Heights₂.Heights.ChartKernel
