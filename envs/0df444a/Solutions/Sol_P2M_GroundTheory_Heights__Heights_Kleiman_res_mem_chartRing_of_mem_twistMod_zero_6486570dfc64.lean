-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_chartRing_of_mem_twistMod_zero_6486570dfc64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:30:14.00261+00:00
-- url     : https://prove2.me/submissions/fd374c73-a2d3-4ae9-ad05-44f54ac0baee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers

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
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I : Chart x} {a : Ω} (ha : a ∈ twistMod S x 0 I) :
    a ∈ chartRing S x I := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [chartRing_smul_def, mul_one]; exact c.2
end GroundTheory.Heights₂.Heights.Kleiman
