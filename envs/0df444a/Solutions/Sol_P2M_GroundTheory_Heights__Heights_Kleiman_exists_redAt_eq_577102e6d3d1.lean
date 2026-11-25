-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_redAt_eq_577102e6d3d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:40.897825+00:00
-- url     : https://prove2.me/submissions/8e1bea0a-e2c8-4eb3-a3a7-4814e07b5f75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redAt_eq_fa1134abb51b

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
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
include hsp
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I : Chart y) {c : K'}
    (hc : c ∈ chartRing k y I) : ∃ a ∈ chartRing k x (liftChart hxy I), redAt k x y a = c := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hc
  exact ⟨aeval x f / aeval x s, ⟨f, s, e, hs, hf, hse, rfl⟩,
    redAt_eq hsp hf hse (eval_ne_zero_of_mem_monos I hs)⟩
end GroundTheory.Heights₂.Heights.Kleiman
