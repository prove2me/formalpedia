-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.star_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:48.06555+00:00
-- url     : https://prove2.me/submissions/2f2a299a-e6d3-4ed0-bba0-5eddb666f363

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution [StarRing E] {x : E} (hx : x ∈ (algebraMap (𝓞 E) E).range) :
    starRingEnd E x ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨o, rfl⟩ := RingHom.mem_range.mp hx
  have hint : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E o)) := by
    first
    | exact (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom
    | exact (o.2).map (starRingEnd E).toIntAlgHom
  exact RingHom.mem_range.mpr ⟨⟨_, hint⟩, rfl⟩
end PI.UnitaryGroupMassFormula.LCG
