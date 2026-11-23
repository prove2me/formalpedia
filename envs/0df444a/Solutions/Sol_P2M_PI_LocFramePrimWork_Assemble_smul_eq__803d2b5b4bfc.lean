-- Prove2me | solution 1 for P2M_PI_LocFramePrimWork_Assemble_smul_eq__803d2b5b4bfc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:26.836249+00:00
-- url     : https://prove2.me/submissions/0f243b6b-2862-4670-bc76-915784a0468b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_Assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
namespace PI.LocFramePrimWork
theorem _root_.solution (t : v.adicCompletionIntegers F) (y : Fv F v ⊗[F] E) :
    t • y = sc (E := E) v (t : Fv F v) * y := by
  change (t : Fv F v) • y = _
  rw [Algebra.smul_def]
  rfl
end PI.LocFramePrimWork
