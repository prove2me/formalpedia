-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_exists_mem_support_1c42fd99ea17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:09:46.662936+00:00
-- url     : https://prove2.me/submissions/32ad3a5b-47ac-4d5a-bf43-bd726c14e3bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport

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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
theorem _root_.solution (hx : x ≠ 0) : ∃ i, i ∈ support x := by
  by_contra h
  simp only [not_exists] at h
  exact hx (funext fun i => by_contra fun hi => h i ((mem_support x).mpr hi))
end GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
