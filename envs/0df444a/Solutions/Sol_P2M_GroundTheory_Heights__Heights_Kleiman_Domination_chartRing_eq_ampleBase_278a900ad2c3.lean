-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_chartRing_eq_ampleBase_278a900ad2c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:34:28.021929+00:00
-- url     : https://prove2.me/submissions/061bc537-8489-4050-9f40-a52ad09c1821

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination

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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution {i : Fin (N + 1)} (hi : x i ≠ 0) :
    chartRing S x (singleChart hi) = ampleBase (S := S) x i := by
  apply le_antisymm
  · intro a ha
    exact mem_ampleBase_of_mem_chartRing hi ha
  · rw [ampleBase, Algebra.adjoin_le_iff]
    rintro _ ⟨l, rfl⟩
    exact (ratio (S := S) hi l).2
end GroundTheory.Heights₂.Heights.Kleiman.Domination
