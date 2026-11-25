-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LocF_proper_d65cdbdea1a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:39:57.173687+00:00
-- url     : https://prove2.me/submissions/299eeffe-18a1-464f-875a-e4f89d1b42ac

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LocF_finite_quot_bc450d17568e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LocF
open NumberField IsDedekindDomain HeightOneSpectrum WithZero
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.BasicNotions.Examples₂.LocF
theorem _root_.solution : ProperSpace (v.adicCompletion F) := by
  have := finite_quot v
  have h1 : IsDiscreteValuationRing (v.adicCompletionIntegers F) := inferInstance
  have h2 := adicInt_residue_finite (K := F) v
  exact Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
    ⟨inferInstance, h1, h2⟩
end Formalism.BasicNotions.Examples₂.LocF
