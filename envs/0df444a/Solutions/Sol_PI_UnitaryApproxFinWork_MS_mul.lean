-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.MS_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:10.52586+00:00
-- url     : https://prove2.me/submissions/ee42845d-cc79-4bbf-ad58-2efb16a3be9e

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
theorem _root_.solution {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)
end PI.UnitaryApproxFinWork
