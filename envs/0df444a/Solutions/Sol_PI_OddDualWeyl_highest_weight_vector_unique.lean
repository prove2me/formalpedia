-- Prove2me | solution 1 for PI.OddDualWeyl.highest_weight_vector_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:16:59.530982+00:00
-- url     : https://prove2.me/submissions/ded4151c-87b3-450c-8fe6-3661405dbeb9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Lemmata_GeneralBFactRightAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightVectorUnique
import Theorems.Thm_PI_OddDualWeyl_Uniq_aeval_smul_hom
import Theorems.Thm_PI_OddDualWeyl_Uniq_dualSub_dualM
import Theorems.Thm_PI_OddDualWeyl_Uniq_det_P_ne

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
open PI.OddDualWeyl
open Uniq
namespace PI.OddDualWeyl
theorem _root_.solution : Uniq := by
  intro K _ k d G hG h0
  by_cases hk : k = 1
  · subst hk
    have hD : ∀ v : Fin 1 × Fin 1, dualM K 1 v.1 v.2 = 1 := by
      intro v; simp only [dualM, adjugate_fin_one, Matrix.of_apply]
      rw [Subsingleton.elim v.2.rev v.1, Matrix.one_apply_eq]
    have hS : dualSub K 1 G = aeval (fun _ => (1 : MvPolynomial (Fin 1 × Fin 1) K)) G := by
      simp only [dualSub, hD]
    have e : G = aeval (fun v : Fin 1 × Fin 1 => X (0, 0) * (1 : MvPolynomial (Fin 1 × Fin 1) K)) G := by
      conv_lhs => rw [← aeval_X_left_apply G]
      exact congrArg (fun f => aeval f G) (funext fun v => by rw [mul_one, Subsingleton.elim v (0, 0)])
    rw [e, aeval_smul_hom hG, ← hS, h0, mul_zero]
  · set c : MvPolynomial (Fin k × Fin k) K := (P _ k).det * (genM K k).det ^ (k - 2)
    have hc : c ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
      · intro h; have := det_P_ne (Rg := MvPolynomial (Fin k × Fin k) K) (k := k); rw [h, zero_mul] at this
        exact zero_ne_one this
      · exact det_mvPolynomialX_ne_zero (Fin k) K
    have e : dualSub K k (dualSub K k G) = c ^ d * G := by
      have : (dualSub K k).comp (dualSub K k) = aeval fun v => c * X v := by
        rw [dualSub, comp_aeval]; congr 1; funext v
        exact dualSub_dualM hk v.1 v.2
      rw [← AlgHom.comp_apply, this, aeval_smul_hom hG, aeval_X_left_apply]
    rw [h0, map_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (pow_ne_zero _ hc)
end PI.OddDualWeyl
