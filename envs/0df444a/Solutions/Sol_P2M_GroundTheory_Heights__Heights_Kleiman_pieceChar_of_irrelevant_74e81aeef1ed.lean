-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_pieceChar_of_irrelevant_74e81aeef1ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:53:17.670026+00:00
-- url     : https://prove2.me/submissions/85c8aeb0-9a1f-47f4-8c4b-5fa4c54a6e8a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_eulerCharQuot_self_9762b655af6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_of_irrelevant_6754bd39d524

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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (pp : Ideal (Poly k N)) (hpp : ∀ i, (X i : Poly k N) ∈ pp) (a : ℤ) {t : ℕ}
    (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ) : pieceChar k pp a L n c = 0 := by
  unfold pieceChar
  rw [twist_idealSys_of_irrelevant pp hpp a]
  exact eulerCharQuot_self _
end GroundTheory.Heights₂.Heights.Kleiman
