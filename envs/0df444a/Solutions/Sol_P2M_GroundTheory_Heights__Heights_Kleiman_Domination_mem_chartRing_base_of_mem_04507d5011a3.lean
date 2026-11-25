-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_chartRing_base_of_mem_04507d5011a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:10:07.478654+00:00
-- url     : https://prove2.me/submissions/f947e1c5-4b7f-44a2-9d71-0156d12bbe4e

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
theorem _root_.solution (z : Ω) (hz : z ∈ chartRing S x' (singleChart hj)) :
    z ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) := by
  have h := mem_ampleBase_of_mem_chartRing (S := S) hj hz
  rw [ampleBase] at h
  clear hz
  induction h using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    exact (ratio (S := chartRing S x (singleChart hi)) hj k).2
  | algebraMap s =>
    exact Subalgebra.algebraMap_mem _ (algebraMap S (chartRing S x (singleChart hi)) s)
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb
end GroundTheory.Heights₂.Heights.Kleiman.Domination
