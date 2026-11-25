-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locMap_locMap_eq_zero_6e4ca001f07c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:57.515058+00:00
-- url     : https://prove2.me/submissions/b6057862-72f5-41a5-9fcd-99c5419b2f1a

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
variable {M'' : Type w} [AddCommGroup M''] [Module (Poly S N) M''] [Module S M'']
  [IsScalarTower S (Poly S N) M'']
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (f : M' →ₗ[Poly S N] M) (g : M →ₗ[Poly S N] M'')
    (hfg : ∀ m, g (f m) = 0) (I : Finset (Fin (N + 1))) (x : LocMod S N M' I) :
    locMap g I (locMap f I x) = 0 := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [locMap_mk, locMap_mk, hfg]
    exact LocalizedModule.zero_mk s
end GroundTheory.Heights₂.Heights.Kleiman
