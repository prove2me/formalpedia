-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CohomRetract_proof_5cc87108e672
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:13.523832+00:00
-- url     : https://prove2.me/submissions/2bf55a47-29e2-4ad2-864c-73a58efb597b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCohomRetract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_retract_fad49f66fb1a

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
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace CohomRetract
theorem _root_.solution : CohomRetract.Statement.{u, v, w} := by
  intro S _ N M M' _ _ _ _ _ _ _ _ 𝓜 𝓜' f g hgf i c
  exact (cohomMap_retract f g hgf i c).injective
end CohomRetract
end GroundTheory.Heights₂.Heights.Kleiman
