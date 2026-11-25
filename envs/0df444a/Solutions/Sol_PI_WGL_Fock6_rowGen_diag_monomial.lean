-- Prove2me | solution 1 for PI.WGL.Fock6.rowGen_diag_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:29.988178+00:00
-- url     : https://prove2.me/submissions/4887ddb6-61e4-499d-8a47-df66b5ec3d1b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftFock
import Theorems.Thm_PI_WGL_Fock6_rowGen_diag_X
import Theorems.Thm_PI_WGL_Fock6_rowGen_diag_C
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
open PI.WGL.Fock6
namespace PI.WGL.Fock6
theorem _root_.solution {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℂ) :
    rowGen ℂ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (wa a) m) := by
  classical
  have hw : Finsupp.weight (wa a) m = ∑ v ∈ m.support, wa (n := n) a v * m v := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_congr rfl (fun v _ => by rw [smul_eq_mul, mul_comm])
  simp only [monomial_eq, Finsupp.prod, map_mul, map_prod, map_pow, rowGen_diag_C, rowGen_diag_X, mul_pow,
    Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, hw]
  ring
end PI.WGL.Fock6
