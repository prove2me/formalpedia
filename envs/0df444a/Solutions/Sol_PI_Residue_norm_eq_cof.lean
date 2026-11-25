-- Prove2me | solution 1 for PI.Residue.norm_eq_cof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:44.251645+00:00
-- url     : https://prove2.me/submissions/c88ccb18-305f-4926-99eb-f6b29341a157

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_DvdSpanOfIdealSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units
open scoped nonZeroDivisors ENNReal Classical
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) :
    mixedEmbedding.norm (x : mixedSpace K) =
      (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) * (Ideal.absNorm (cof J x) : ℝ) := by
  rw [← Nat.cast_mul, ← map_mul, ← cof_spec, Ideal.absNorm_span_singleton,
    ← idealSetMap_apply K J x, ← intNorm_coe, intNorm]
end PI.Residue
