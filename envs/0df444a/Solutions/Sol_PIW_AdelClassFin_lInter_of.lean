-- Prove2me | solution 1 for PIW.AdelClassFin.lInter_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:20:43.045076+00:00
-- url     : https://prove2.me/submissions/7400c4e1-10f7-464f-81d3-af43bd564220

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat
import Theorems.Thm_PIW_AdelClassFin_DictLat_hhat_iv
import Theorems.Thm_PIW_AdelClassFin_dual_hat_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (h : DInter) : LInter := by
  intro I v hv
  rw [I.L_dual]
  intro y hy
  apply h I.F I.E
  rw [← DictLat.hhat_iv]
  exact dual_hat_integral I _ (DictLat.iv_mem I hy) _ hv
end PIW.AdelClassFin
