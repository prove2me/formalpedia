-- Prove2me | solution 1 for PI.LPI.prV_sum_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:59:22.376047+00:00
-- url     : https://prove2.me/submissions/d4c01f2a-bfa2-405f-8c91-99f5c1ec854d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVSumTmul
import Theorems.Thm_PI_LPI_prV_tmul

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
    (v : HeightOneSpectrum (𝓞 F)) {k : ℕ} (e : Fin k → E) (a : Fin k → FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (∑ i, e i ⊗ₜ[F] a i) = ∑ i, e i ⊗ₜ[F] a i v := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => prV_tmul v (e i) (a i)
end PI.LPI
