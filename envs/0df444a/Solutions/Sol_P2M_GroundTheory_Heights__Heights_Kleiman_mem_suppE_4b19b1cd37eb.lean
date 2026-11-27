-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_suppE_4b19b1cd37eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:03:19.231902+00:00
-- url     : https://prove2.me/submissions/48520cea-15ae-4fc0-bbe9-34df3a672d1d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone

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
variable (S : Type u) [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
variable {S x E}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {w : ConeE S x E} {d : ℤ} : d ∈ suppE w ↔ coeffE S x E d w ≠ 0 :=
  Finsupp.mem_support_iff
end GroundTheory.Heights₂.Heights.Kleiman
