-- Prove2me | solution 1 for PI.LocFramePrimWork.Assemble_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:37.809332+00:00
-- url     : https://prove2.me/submissions/5d5d1883-6e94-4bd6-b998-917be4b30134

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
theorem _root_.solution (t : v.adicCompletionIntegers F) (x : Fin n → Fv F v ⊗[F] E) :
    t • x = sc (E := E) v (t : Fv F v) • x := by
  funext i
  change (t : Fv F v) • x i = sc (E := E) v (t : Fv F v) * x i
  rw [Algebra.smul_def]
  rfl
end PI.LocFramePrimWork
