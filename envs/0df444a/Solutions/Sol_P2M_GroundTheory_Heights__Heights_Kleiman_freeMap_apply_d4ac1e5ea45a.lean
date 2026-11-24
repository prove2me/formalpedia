-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_apply_d4ac1e5ea45a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:57.000212+00:00
-- url     : https://prove2.me/submissions/4893c0d5-2dfe-499f-afef-02a86ca8e923

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto

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
universe u v w w'
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
omit [Module S M] [IsScalarTower S (Poly S N) M]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {r : ℕ} (g : Fin r → M) (f : Fin r → Poly S N) :
    freeMap S N g f = ∑ j, f j • g j := by
  simp [freeMap]
end GroundTheory.Heights₂.Heights.Kleiman
