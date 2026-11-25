-- Prove2me | solution 1 for ReciprocityTheory.P1.isAdicComplete_comap_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:07:40.075538+00:00
-- url     : https://prove2.me/submissions/2d1344be-2fe1-4520-ad8e-774113fd9876

import Mathlib
import Definitions.Def_ReciprocityTheory_AdicCompleteness_IsAdicCompleteComapConstantCoeff
import Theorems.Thm_ReciprocityTheory_P1_isHausdorff_comap_constantCoeff
import Theorems.Thm_ReciprocityTheory_P1_isPrecomplete_comap_constantCoeff

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
variable {A : Type*} [CommRing A] (I : Ideal A)
namespace ReciprocityTheory.P1
theorem _root_.solution [IsAdicComplete I A] :
    IsAdicComplete (I.comap (constantCoeff (R := A))) A⟦X⟧ :=
  { isHausdorff_comap_constantCoeff I, isPrecomplete_comap_constantCoeff I with }
end ReciprocityTheory.P1
