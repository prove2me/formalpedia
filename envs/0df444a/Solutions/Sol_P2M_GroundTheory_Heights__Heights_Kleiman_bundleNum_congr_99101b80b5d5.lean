-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_congr_99101b80b5d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:46.729438+00:00
-- url     : https://prove2.me/submissions/89d98e23-d195-4417-9d7f-acd2159b2e89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg

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
open MvPolynomial Filter
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (pp : Ideal (Poly k N)) {n : ℕ} {L L' : Fin n → LineBundle k x}
    (h : ∀ i, (L i).toSubSystem = (L' i).toSubSystem) : bundleNum pp L = bundleNum pp L' := by
  unfold bundleNum
  rw [funext h]
end GroundTheory.Heights₂.Heights.Kleiman
