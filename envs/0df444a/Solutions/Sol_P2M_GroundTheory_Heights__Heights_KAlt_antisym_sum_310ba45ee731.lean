-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_antisym_sum_310ba45ee731
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:00:04.815342+00:00
-- url     : https://prove2.me/submissions/56ecfed7-ad07-406b-a4af-8bcf64f0d2f7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush

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
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.KAlt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution {κ : Type*} (s : Finset κ) (f : κ → MvPolynomial ι ℚ) :
    antisym (∑ x ∈ s, f x) = ∑ x ∈ s, antisym (f x) := by
  simp only [antisym, map_sum, smul_sum]
  rw [sum_comm]
end GroundTheory.Heights₂.Heights.KAlt
