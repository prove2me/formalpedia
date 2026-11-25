-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_interNum_comp_perm_080c53d7c885
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:59.457848+00:00
-- url     : https://prove2.me/submissions/123bf498-aba4-4c11-b0e3-f38c939699aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_InterSumEventuallyEqInterNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interSum_comp_perm_f2b5c16a64c2

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (σ : Equiv.Perm (Fin n)) :
    interNum pp (fun i => L (σ i)) = interNum pp L := by
  unfold interNum
  congr 1
  funext c
  exact interSum_comp_perm pp L σ c
end GroundTheory.Heights₂.Heights.Kleiman
