-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_eval_map_firstGroup_16f555f9d2cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:16.655811+00:00
-- url     : https://prove2.me/submissions/cc8ff5dd-7369-4eb0-a06b-0bf1d63b8d00

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormSep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartNormAlgClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_algebraMap_localization_C_eccb7f2840c7

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
open GroundTheory.Heights₂.Heights.ChartNormAlgClosed
namespace GroundTheory.Heights₂.Heights.ChartNormAlgClosed
theorem _root_.solution {F : Type} [Field F] {n e : ℕ} (p : Ideal (MvPolynomial (Fin e × Fin n) F))
    [p.IsPrime] (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F) :
    eval (fun m => algebraMap F (Localization.AtPrime p) (u m))
        (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) (firstGroup f)) =
      algebraMap _ (Localization.AtPrime p) (specFirst f u) := by
  rw [eval_map]
  simp only [firstGroup, specFirst]
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, bind₁_C_right, MvPolynomial.algebraMap_apply, eval₂_C, MvPolynomial.algebraMap_eq]
  | add a b ha hb =>
    rw [map_add, map_add, eval₂_add, ha, hb, map_add]
  | mul_X a ij ha =>
    rw [map_mul, map_mul, eval₂_mul, ha, map_mul, aeval_X, bind₁_X_right]
    congr 1
    obtain ⟨i, m⟩ := ij
    cases i using Fin.cases with
    | zero => simp [specFirstVar, algebraMap_localization_C]
    | succ i => simp [specFirstVar]
end GroundTheory.Heights₂.Heights.ChartNormAlgClosed
