-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locResS_comp_aed20a079c45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:02:22.526232+00:00
-- url     : https://prove2.me/submissions/3de4f506-b976-4051-a3b9-73964706e29c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq

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
universe u v
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (I J K : StdCell N) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1) :
    (locResS (S := S) (M := M) J K hJK).comp (locResS I J hIJ) = locResS I K (hIJ.trans hJK) := by
  refine LinearMap.ext fun x => ?_
  induction x using LocalizedModule.induction_on with
  | h m s =>
    change locRes hJK (locRes hIJ _) = locRes (hIJ.trans hJK) _
    rw [locRes_mk, locRes_mk, locRes_mk]
end GroundTheory.Heights₂.Heights.Kleiman
