-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_res_ampleChart_pow_e61756f6a50e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:00.999629+00:00
-- url     : https://prove2.me/submissions/f57159ae-d335-4655-8825-b1155b35e7e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_ampleChart_mul_d12ec9174181
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_chartRing_sub_ampleChart_80ef58d2b323

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
theorem _root_.solution {a : Ω} (ha : a ∈ ampleChart H 1 σ I) (n : ℕ) :
    a ^ n ∈ ampleChart H 1 σ I := by
  induction n with
  | zero => rw [pow_zero]; exact res_chartRing_sub_ampleChart (one_mem _)
  | succ n ih => rw [pow_succ]; exact res_ampleChart_mul ih ha
end GroundTheory.Heights₂.Heights.Kleiman
