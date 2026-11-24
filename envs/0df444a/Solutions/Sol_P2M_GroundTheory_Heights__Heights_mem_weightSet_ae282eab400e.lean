-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_weightSet_ae282eab400e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:45.190198+00:00
-- url     : https://prove2.me/submissions/9d65f731-e444-4954-8ded-63c4229b0cc3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree

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
open MvPolynomial
noncomputable section
variable {R σ : Type*} [CommRing R] {w : σ → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {p : MvPolynomial σ R} {a : ℕ} :
    a ∈ weightSet w p ↔ ∃ d ∈ p.support, Finsupp.weight w d = a := by
  unfold weightSet
  exact Finset.mem_image
end GroundTheory.Heights₂.Heights
