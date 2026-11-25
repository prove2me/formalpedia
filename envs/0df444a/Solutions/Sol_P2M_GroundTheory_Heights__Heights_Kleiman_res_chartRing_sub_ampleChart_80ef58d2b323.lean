-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_res_chartRing_sub_ampleChart_80ef58d2b323
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:56:28.568221+00:00
-- url     : https://prove2.me/submissions/9f78fc8f-4626-45f8-a228-8a65ee843520

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_twistMod_zero_of_mem_chartRing_abfe75d5ce93

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {H : SubSystem S x Ω} {σ : Ω} {I : Chart x}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {a : Ω} (ha : a ∈ chartRing S x I) : a ∈ ampleChart H 1 σ I :=
  ⟨0, by rw [pow_zero, mul_one, mul_zero]; exact res_mem_twistMod_zero_of_mem_chartRing ha⟩
end GroundTheory.Heights₂.Heights.Kleiman
