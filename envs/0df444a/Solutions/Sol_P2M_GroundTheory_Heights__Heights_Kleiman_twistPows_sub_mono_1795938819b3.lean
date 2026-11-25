-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twistPows_sub_mono_1795938819b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:21:16.586865+00:00
-- url     : https://prove2.me/submissions/fcf7b09f-2f22-420e-ae79-a3a96b8c3dd7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotDevissage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_mono_a1444dbbcbc5

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {F G : SubSystem S x E} (h : ∀ I, F.sub I ≤ G.sub I) :
    ∀ (t : ℕ) (L : Fin t → SubSystem S x Ω) (n : Fin t → ℕ) (I : Chart x),
      (F.twistPows t L n).sub I ≤ (G.twistPows t L n).sub I
  | 0, _, _, I => h I
  | t + 1, _, _, I => twist_sub_mono (solution h t _ _) _ I
end GroundTheory.Heights₂.Heights.Kleiman
