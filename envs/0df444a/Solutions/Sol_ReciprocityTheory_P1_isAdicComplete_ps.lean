-- Prove2me | solution 1 for ReciprocityTheory.P1.isAdicComplete_ps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:42.045797+00:00
-- url     : https://prove2.me/submissions/c706b2c8-6d8e-439f-b3a0-508bd34e4e88

import Mathlib
import Definitions.Def_ReciprocityTheory_AdicCompleteness_IsAdicCompleteComapConstantCoeff
import Theorems.Thm_ReciprocityTheory_P1_isAdicComplete_comap_constantCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open PowerSeries IsLocalRing
noncomputable section
open ReciprocityTheory ReciprocityTheory.P1
namespace ReciprocityTheory.P1
theorem _root_.solution {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal R⟦X⟧) R⟦X⟧ := by
  have h : maximalIdeal R⟦X⟧ = (maximalIdeal R).comap (constantCoeff (R := R)) := by
    ext f
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_iff_constantCoeff]
  rw [h]
  exact isAdicComplete_comap_constantCoeff _
end ReciprocityTheory.P1
