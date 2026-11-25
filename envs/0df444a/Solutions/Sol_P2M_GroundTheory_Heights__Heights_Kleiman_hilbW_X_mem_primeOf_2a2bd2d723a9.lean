-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_hilbW_X_mem_primeOf_2a2bd2d723a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:08:56.419404+00:00
-- url     : https://prove2.me/submissions/62e93346-9cdf-470e-8741-90d39a26bb76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedSectionsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedNumbersSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumPointSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropHilbW
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
open MvPolynomial Filter
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (x : Fin (N + 1) → Ω) {i : Fin (N + 1)} (hi : x i = 0) :
    (X i : Poly S N) ∈ primeOf (S := S) x := by
  rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X S i), aeval_X, hi]
end GroundTheory.Heights₂.Heights.Kleiman
