-- Prove2me | solution 1 for PI.FJMA.bCol_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:27.035616+00:00
-- url     : https://prove2.me/submissions/1fa18f68-05f6-4624-8251-2aea50458b7a

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
theorem _root_.solution {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (F G : MvPolynomial σ ℂ)
    (hF : ∀ x, pderiv (ι x) F = 0) : bCol ι c d (F * G) = F * bCol ι c d G := by
  unfold bCol
  simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, hF, smul_eq_mul, mul_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)
end PI.FJMA
