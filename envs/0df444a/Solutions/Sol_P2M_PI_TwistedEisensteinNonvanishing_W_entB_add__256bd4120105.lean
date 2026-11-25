-- Prove2me | solution 1 for P2M_PI_TwistedEisensteinNonvanishing_W_entB_add__256bd4120105
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:31.525647+00:00
-- url     : https://prove2.me/submissions/182ffe3a-78a6-45bf-90f8-cf39dae69356

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TestFunctionPeriodicity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {N' N : ℕ} (q k₀ c' n' c n : ℕ) (x y : HomE E N' N) (p p' : ℕ) :
    entB q k₀ c' n' c n 0 0 (x + y) p p' = entB q k₀ c' n' c n 0 0 x p p' + entB q k₀ c' n' c n 0 0 y p p' := by
  unfold entB atN
  split_ifs <;> simp [add_mul]
end PI.TwistedEisensteinNonvanishing.W
