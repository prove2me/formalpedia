-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.MS_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:15.906205+00:00
-- url     : https://prove2.me/submissions/d702051a-c058-4705-a281-05c561587646

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SigmaMemIntOE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n : Type} [Fintype n] [DecidableEq n]
variable {v : HeightOneSpectrum (𝓞 F)}
namespace PI.UnitaryApproxFinWork
theorem _root_.solution {a : E ⊗[F] v.adicCompletion F} (ha : a ∈ Sv E v)
    {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) : MS E v (a • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ ha (hM i j)
end PI.UnitaryApproxFinWork
