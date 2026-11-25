-- Prove2me | solution 1 for P2M_PIW_AdelClassFin_hform_swap__d33b9707c34f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:26.900404+00:00
-- url     : https://prove2.me/submissions/8caa9a7a-4de4-41ee-97af-1fa9ad2b2760

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSmulRight
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
variable {E : Type} [Field E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
namespace PIW.AdelClassFin
theorem _root_.solution (hJ : IsHerm (starRingEnd E) J) (x y : Fin m → E) :
    hform (starRingEnd E) J y x = star (hform (starRingEnd E) J x y) := by
  have hJ' : ∀ i j, J i j = star (J j i) := by
    intro i j
    have h := congrFun (congrFun hJ i) j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply] at h
    exact h.symm
  unfold hform
  simp only [starRingEnd_apply, star_sum, star_mul', star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ' j i]
  ring
end PIW.AdelClassFin
