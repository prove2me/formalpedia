-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.MS_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:13.402387+00:00
-- url     : https://prove2.me/submissions/dd9a26a5-adcd-40f5-a863-476ba1814ec4

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
theorem _root_.solution : MS E v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _
end PI.UnitaryApproxFinWork
