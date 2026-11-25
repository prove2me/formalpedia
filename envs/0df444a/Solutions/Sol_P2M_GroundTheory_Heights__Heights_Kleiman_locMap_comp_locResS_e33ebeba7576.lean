-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locMap_comp_locResS_e33ebeba7576
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:53.513366+00:00
-- url     : https://prove2.me/submissions/27d1757a-2019-434d-9940-b6b0c4848805

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact

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
universe w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (f : M →ₗ[Poly S N] M') (I J : StdCell N) (h : I.1 ⊆ J.1)
    (x : LocMod S N M I.1) : locMap f J.1 (locResS I J h x) = locResS I J h (locMap f I.1 x) := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    change locMap f J.1 (locRes h _) = locRes h (locMap f I.1 _)
    rw [locRes_mk, locMap_mk, locMap_mk, locRes_mk]
end GroundTheory.Heights₂.Heights.Kleiman
