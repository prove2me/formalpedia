-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_ampleChart_single_iff_f5349f989973
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:32.638171+00:00
-- url     : https://prove2.me/submissions/419dc01c-20eb-4c9b-853f-888851071b27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_chartRing_eq_ampleBase_278a900ad2c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_div_mem_of_mem_pullPow_8800596b5cce

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
theorem _root_.solution (a : Ω) :
    a ∈ ampleChart (pullSys (S := S) x x') 1 (x i) (singleChart hj) ↔
      a ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) := by
  constructor
  · intro ha
    rw [mem_ampleChart_iff] at ha
    obtain ⟨n, hn⟩ := ha
    have h := div_mem_of_mem_pullPow hi hj n hn
    rwa [mul_div_assoc, div_self (pow_ne_zero n hi), mul_one] at h
  · intro ha
    have hA : chartRing S x (singleChart hi) ≤ ampleSub (S := S) (x := x) (singleChart hj) i := by
      rw [chartRing_eq_ampleBase hi, ampleBase, Algebra.adjoin_le_iff]
      rintro _ ⟨l, rfl⟩
      show _ ∈ ampleChart _ _ _ _
      rw [mem_ampleChart_iff]
      refine ⟨1, ?_⟩
      rw [pow_one, div_mul_cancel₀ _ hi]
      exact coord_mem_pullPow_one _ l
    have h := mem_ampleBase_of_mem_chartRing (S := chartRing S x (singleChart hi)) hj ha
    rw [ampleBase] at h
    clear ha
    induction h using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      rw [mem_ampleChart_iff]
      refine ⟨0, ?_⟩
      rw [pow_zero, mul_one, mem_pullPow_zero_iff]
      exact (ratio (S := S) hj k).2
    | algebraMap a0 => exact hA a0.2
    | add a b _ _ ha hb => exact (ampleSub (S := S) (x := x) (singleChart hj) i).add_mem ha hb
    | mul a b _ _ ha hb => exact (ampleSub (S := S) (x := x) (singleChart hj) i).mul_mem ha hb
end GroundTheory.Heights₂.Heights.Kleiman.Domination
