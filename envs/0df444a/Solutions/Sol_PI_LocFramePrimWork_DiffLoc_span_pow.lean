-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:09.572233+00:00
-- url     : https://prove2.me/submissions/a326f201-6b8c-477d-a060-f30186f35937

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc

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
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocFramePrimWork
theorem _root_.solution (c : Fv F v ⊗[F] E) (k : ℕ) :
    (Submodule.span (v.adicCompletionIntegers F) {c}) ^ k =
      Submodule.span (v.adicCompletionIntegers F) {c ^ k} := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Submodule.one_eq_span]
  | succ k ih => rw [pow_succ, ih, Submodule.span_mul_span, Set.singleton_mul_singleton, pow_succ]
end PI.LocFramePrimWork
