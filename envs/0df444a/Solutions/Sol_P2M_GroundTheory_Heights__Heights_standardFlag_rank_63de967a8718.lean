-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_standardFlag_rank_63de967a8718
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:11:30.095339+00:00
-- url     : https://prove2.me/submissions/8ae7a69b-e4b6-4788-a13c-3bbde58cd06c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (i : Fin 3) :
    (HermitianBundle.standard K 2).rank (standardFlag K i) = i := by
  fin_cases i
  · change Module.finrank (𝓞 K) (⊥ : Submodule (𝓞 K) (Fin 2 → 𝓞 K)) = 0
    simp
  · change Module.finrank (𝓞 K) (LinearMap.range (firstIncl K)) = 1
    rw [← (LinearEquiv.ofInjective (firstIncl K) firstIncl_injective).finrank_eq,
      Module.finrank_self]
  · change Module.finrank (𝓞 K) (⊤ : Submodule (𝓞 K) (Fin 2 → 𝓞 K)) = 2
    rw [finrank_top, Module.finrank_fin_fun]
end GroundTheory.Heights₂.Heights
