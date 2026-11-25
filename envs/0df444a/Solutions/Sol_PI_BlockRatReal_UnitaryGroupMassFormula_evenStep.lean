-- Prove2me | solution 1 for PI.BlockRatReal.UnitaryGroupMassFormula.evenStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:41.597387+00:00
-- url     : https://prove2.me/submissions/e0643565-0223-4757-91e9-c2946af589c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_NuOfAntitone
import Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_nuOf_antitone
import Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_det_map_ne
import Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_eval_map_rowAct
import Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_map_map_int
import Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_s1
import Theorems.Thm_PI_BlockRatReal_UnitaryGroupMassFormula_s2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.BlockRatReal PI.BlockRatReal.UnitaryGroupMassFormula
namespace PI.BlockRatReal.UnitaryGroupMassFormula
theorem _root_.solution : EvenStep := by
  intro m LL _ embLL lam hl M0 f hf
  refine ⟨C (M0.1.det ^ (-lam (Fin.last m))) * Formalism.GradedWeylDivisibility.rowAct LL (↑M0⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)
    (MvPolynomial.map (Int.castRingHom LL) f), ?_, fun y _ => ?_⟩
  · rw [MvPolynomial.C_mul']
    exact Submodule.smul_mem _ _ (s2 _ _ _ _ (s1 _ _ _ (nuOf_antitone hl) f hf))
  · have hd := det_map_ne embLL M0
    have hmul : (↑M0⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map embLL * (M0.1.map embLL * y) = y := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, M0.inv_mul, Matrix.map_one embLL (map_zero _) (map_one _),
        Matrix.one_mul]
    have hc : embLL (M0.1.det ^ (-lam (Fin.last m))) = (M0.1.map embLL).det ^ (-lam (Fin.last m)) := by
      rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]
    rw [map_mul, map_C, eval_mul, eval_C, eval_map_rowAct, hmul, map_map_int, hc, Matrix.det_mul, mul_zpow,
      _root_.zpow_neg]
    field_simp
end PI.BlockRatReal.UnitaryGroupMassFormula
