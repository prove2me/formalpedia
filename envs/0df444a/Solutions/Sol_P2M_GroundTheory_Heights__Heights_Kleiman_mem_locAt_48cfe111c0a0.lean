-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_locAt_48cfe111c0a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:56:41.280645+00:00
-- url     : https://prove2.me/submissions/64d2f51a-c7a7-4534-b539-2fbf3ef331d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal

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
theorem _root_.solution {f s : Poly k N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s.IsHomogeneous e)
    (h : aeval y s ≠ 0) : aeval x f / aeval x s ∈ locAt k x y :=
  ⟨f, s, e, hf, hs, h, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman
