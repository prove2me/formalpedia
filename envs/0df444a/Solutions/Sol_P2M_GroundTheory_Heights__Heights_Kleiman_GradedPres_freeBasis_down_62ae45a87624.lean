-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_freeBasis_down_62ae45a87624
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:36.602539+00:00
-- url     : https://prove2.me/submissions/aec02bf9-6269-41b0-acb1-d0585d6bfbb2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGradedPres

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
namespace GroundTheory.Heights₂.Heights.Kleiman.GradedPres
theorem _root_.solution (j : Fin r) : (freeBasis.{u, v} S N r j).down = Pi.single j 1 := by
  rw [freeBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl
end GroundTheory.Heights₂.Heights.Kleiman.GradedPres
