-- Prove2me | solution 1 for PI.FJMA.bRow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:31.220143+00:00
-- url     : https://prove2.me/submissions/8f089646-a638-42f3-b98e-92783a3add01

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMA
open PI.FJM
variable {σ : Type}
namespace PI.FJMA
theorem _root_.solution {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (F G : MvPolynomial σ ℂ)
    (hF : ∀ x, pderiv (ι x) F = 0) : bRow ι a b (F * G) = F * bRow ι a b G := by
  unfold bRow
  simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, hF, smul_eq_mul, mul_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)
end PI.FJMA
