-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_genMap_basis_f97c744f41c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:01:46.495809+00:00
-- url     : https://prove2.me/submissions/b9f803b6-51bd-4702-bb11-8e9ca87736c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGradedPres
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_down_62ae45a87624

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
open GroundTheory.Heights₂.Heights.Kleiman.GradedPres
variable {S : Type u} [CommRing S] {N : ℕ}
variable {r : ℕ}
variable {M : Type w} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
namespace GroundTheory.Heights₂.Heights.Kleiman.GradedPres
theorem _root_.solution (𝓜 : GradedPMod S N M) (d : Fin r → ℤ) (m : Fin r → M)
    (hm : ∀ j, m j ∈ 𝓜.piece (d j)) (j : Fin r) :
    (genMap.{u, v} 𝓜 d m hm).toLin (freeBasis.{u, v} S N r j) = m j := by
  classical
  change Fintype.linearCombination (Poly S N) m (freeBasis.{u, v} S N r j).down = m j
  rw [freeBasis_down, Fintype.linearCombination_apply_single, one_smul]
end GroundTheory.Heights₂.Heights.Kleiman.GradedPres
