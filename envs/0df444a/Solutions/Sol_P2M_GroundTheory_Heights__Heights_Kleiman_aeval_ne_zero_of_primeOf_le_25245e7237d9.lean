-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_aeval_ne_zero_of_primeOf_le_25245e7237d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:56:47.939771+00:00
-- url     : https://prove2.me/submissions/6cd33a7c-b559-47a5-a0d3-a569e760dc41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K')
variable {k x y}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
    {s : Poly k N} {e : ℕ} (hs : s.IsHomogeneous e) (h : aeval y s ≠ 0) : aeval x s ≠ 0 := fun h0 =>
  h ((mem_primeOf_of_isHomogeneous y hs).mp (hsp ((mem_primeOf_of_isHomogeneous x hs).mpr h0)))
end GroundTheory.Heights₂.Heights.Kleiman
