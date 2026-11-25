-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__star_mem_integers_6f5fb9ce5b0a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:31:02.155568+00:00
-- url     : https://prove2.me/submissions/15b50d40-c933-413f-a36e-5a0e056f9290

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField NumberField.mixedEmbedding Formalism.HermitianLatticesTheory
open scoped nonZeroDivisors NNReal ENNReal
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] {a : K}
    (ha : a ∈ Set.range (algebraMap (𝓞 K) K)) : star a ∈ Set.range (algebraMap (𝓞 K) K) := by
  obtain ⟨o, rfl⟩ := ha
  have hint : IsIntegral ℤ (star (algebraMap (𝓞 K) K o)) :=
    (NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd K).toIntAlgHom
  exact ⟨⟨star (algebraMap (𝓞 K) K o), hint⟩, rfl⟩
end Formalism.MainNotions.BridgeLemma₂
