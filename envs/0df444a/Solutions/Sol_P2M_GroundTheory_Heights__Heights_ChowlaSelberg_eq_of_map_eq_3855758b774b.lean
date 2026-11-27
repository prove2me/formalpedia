-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_eq_of_map_eq_3855758b774b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:31.771823+00:00
-- url     : https://prove2.me/submissions/60790078-71ef-4860-a740-56a63589117e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PWIdealField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_le_of_map_le_a6eb8b4ef036

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
theorem _root_.solution {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']
    (j : F →+* F') {A B : Ideal (𝓞 F)} (hB : B ≠ ⊥)
    (h : A.map (RingOfIntegers.mapRingHom j) = B.map (RingOfIntegers.mapRingHom j)) : A = B := by
  have hA : A ≠ ⊥ := by
    rintro rfl
    rw [Ideal.map_bot, eq_comm, Ideal.map_eq_bot_iff_of_injective] at h
    · exact hB h
    · intro x y hxy
      exact RingOfIntegers.ext (j.injective (by simpa using congrArg (fun t : 𝓞 F' ↦ (t : F')) hxy))
  exact le_antisymm (le_of_map_le j hB h.le) (le_of_map_le j hA h.ge)
end GroundTheory.Heights₂.Heights.ChowlaSelberg
