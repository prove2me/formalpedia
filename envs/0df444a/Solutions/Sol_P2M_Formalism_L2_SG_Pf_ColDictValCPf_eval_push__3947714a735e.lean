-- Prove2me | solution 1 for P2M_Formalism_L2_SG_Pf_ColDictValCPf_eval_push__3947714a735e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:45:13.561706+00:00
-- url     : https://prove2.me/submissions/08f6cc92-b71a-46a7-9aa6-be18fdffd6c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivisorClosedHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (φ : Module.Dual ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ)) (x : Fin n × Fin n → ℂ)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (Fin n × Fin n) ℂ)) :
    eval x (pushφ φ Q) = φ (map (eval x) Q) := by
  conv_rhs => rw [Q.as_sum]
  rw [pushφ, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_monomial, smul_eval]
  have : (monomial m (eval x (Q.coeff m)) : MvPolynomial (ι × Fin n × Fin n) ℂ) = eval x (Q.coeff m) • monomial m 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]
end Formalism.L2.SG.Pf.ColDictValCPf
