-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_chartRing_base_of_base_f1a1460fb985
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:10:01.801829+00:00
-- url     : https://prove2.me/submissions/50e893c4-53f7-4863-800f-71e1bbb8b7e3

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
variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution (z : Ω) (hz : z ∈ chartRing S x (singleChart hi)) :
    z ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) :=
  Subalgebra.algebraMap_mem _ (⟨z, hz⟩ : chartRing S x (singleChart hi))
end GroundTheory.Heights₂.Heights.Kleiman.Domination
