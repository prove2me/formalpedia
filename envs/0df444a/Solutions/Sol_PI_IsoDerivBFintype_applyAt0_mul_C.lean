-- Prove2me | solution 1 for PI.IsoDerivBFintype.applyAt0_mul_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:13.271847+00:00
-- url     : https://prove2.me/submissions/a2940652-8736-4107-838c-63adf560b207

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
import Theorems.Thm_PI_IsoDerivBFintype_applyAt0_C_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.IsoDerivBFintype
open PI.IsoDerivB
variable {T : Type} [Fintype T] {N N' : ℕ} (Θ : VC T N N' → ℂ)
namespace PI.IsoDerivBFintype
theorem _root_.solution (c : ℂ) (P : MvPolynomial (Idx T N N') ℂ) :
    applyAt0 (P * MvPolynomial.C c) Θ = applyAt0 P Θ * c := by
  rw [mul_comm, applyAt0_C_mul, mul_comm]
end PI.IsoDerivBFintype
