-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.qF_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:36.56509+00:00
-- url     : https://prove2.me/submissions/b6f41008-ee92-497c-863d-7c7e37c65627

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_ofFn_prod_sum
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_ofFn_prod_smul
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_intCast_mul_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_sum_fun_eq_sum_perm
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_det_sub_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_det_sub_noninj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open Finset
open scoped Matrix
namespace PI.UnitaryGroupMassFormula.DSIC
theorem _root_.solution {R : Type*} [Ring R] [Algebra ℂ R] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (F : ℂ → Fin n → Fin n → R) (u : ℂ) :
    qF (fun x a b => ∑ c, A a c • F x c b) u = A.det • qF F u := by
  classical
  unfold qF
  simp_rw [ofFn_prod_sum, ofFn_prod_smul, intCast_mul_eq, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, det_sub_eq]
  rw [sum_fun_eq_sum_perm (fun c => (A.submatrix id c).det • (List.ofFn fun k : Fin n => F (u - (k : ℂ)) (c k) k).prod)
    (fun c hc => by rw [det_sub_noninj A c hc, zero_smul])]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Matrix.det_permute', mul_comm, mul_smul]
end PI.UnitaryGroupMassFormula.DSIC
