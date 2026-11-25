-- Prove2me | solution 1 for PI.LPI.prV_sigR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:29.794035+00:00
-- url     : https://prove2.me/submissions/25015da9-8e19-4247-9360-70fba0da0fab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVSumTmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_SingleApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
open PI PI.LPI
open Formalism.UG
namespace PI.LPI
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (sigR σ (FiniteAdeleRing (𝓞 F) F) z) = sigR σ (v.adicCompletion F) (prV v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a => simp [prV, sigR, evalV, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
end PI.LPI
