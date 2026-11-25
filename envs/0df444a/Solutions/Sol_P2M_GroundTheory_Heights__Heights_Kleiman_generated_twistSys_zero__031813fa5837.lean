-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_generated_twistSys_zero__031813fa5837
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:16.538978+00:00
-- url     : https://prove2.me/submissions/3a6d42cb-49c2-4711-8d15-6bfaea9768ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero

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
variable (k : Type u) [Field k]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} : (twistSys S x 0).Generated := by
  have h1 : (1 : Ω) ∈ (twistSys S x 0).secs := by
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    exact one_mem_twistMod_zero I
  intro I
  obtain ⟨i, hi⟩ := I.2.1
  apply le_antisymm
  · refine Submodule.span_le.mpr fun z hz => ?_
    rw [SubSystem.secs, SetLike.mem_coe, Submodule.mem_iInf] at hz
    exact hz I
  · change twistMod S x 0 I ≤ _
    rw [twistMod_eq_span 0 I hi, zpow_zero]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr h1)
end GroundTheory.Heights₂.Heights.Kleiman
