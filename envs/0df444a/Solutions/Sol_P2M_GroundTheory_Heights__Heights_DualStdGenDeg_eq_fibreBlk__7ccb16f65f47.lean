-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualStdGenDeg_eq_fibreBlk__7ccb16f65f47
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:46.323854+00:00
-- url     : https://prove2.me/submissions/b378954b-4eb2-496f-8cb0-7e52b19b8130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdGenDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial
open GroundTheory.Heights₂.Heights.DualStdGenDeg
namespace GroundTheory.Heights₂.Heights.DualStdGenDeg
theorem _root_.solution (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) : k = fibreBlk₀ := by
  rcases k with ⟨⟨⟩ | ⟨⟩, h⟩
  · rfl
  · exact absurd ⟨(), rfl⟩ h
end GroundTheory.Heights₂.Heights.DualStdGenDeg
