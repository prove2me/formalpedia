-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_IsNumPolyLT_congr_525cd32145d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:03:28.28094+00:00
-- url     : https://prove2.me/submissions/43f9830d-4bbf-45be-9552-b7618952691e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper

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
universe u v w
variable {k : Type u} [Field k] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace IsNumPolyLT
theorem _root_.solution {t D : ℕ} {f g : (Fin t → ℕ) → ℤ → ℚ} (h : IsNumPolyLT t D f)
    (hfg : ∀ n c, f n c = g n c) : IsNumPolyLT t D g := by
  obtain ⟨Q, hQ, hev⟩ := h
  exact ⟨Q, hQ, fun n c => (hfg n c).symm.trans (hev n c)⟩
end IsNumPolyLT
end GroundTheory.Heights₂.Heights.Kleiman
