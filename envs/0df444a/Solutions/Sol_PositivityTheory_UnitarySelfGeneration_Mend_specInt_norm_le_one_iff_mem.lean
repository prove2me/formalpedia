-- Prove2me | solution 1 for PositivityTheory.UnitarySelfGeneration.Mend.specInt_norm_le_one_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:11.355797+00:00
-- url     : https://prove2.me/submissions/e892edbb-d665-4f81-bfc1-2c34a9d58817

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_HomogeneousNonvanishing_SpectralNormIntegrality_SpecInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open PositivityTheory PositivityTheory.UnitarySelfGeneration PositivityTheory.UnitarySelfGeneration.Mend
namespace PositivityTheory.UnitarySelfGeneration.Mend
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) : ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff
end PositivityTheory.UnitarySelfGeneration.Mend
