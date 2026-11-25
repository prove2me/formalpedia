-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_toKer_bijective_f431c159934d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:31:26.684587+00:00
-- url     : https://prove2.me/submissions/841fa4f0-f1ba-44c6-8ae0-f62b5bd49076

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_cocycle_coe_eq_7f2cd17ef32c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_exists_mem_support_1c42fd99ea17

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
theorem _root_.solution (F : SubSystem S x E) (hx : x ≠ 0) : Function.Bijective (toKer F) := by
  obtain ⟨i₀, hi₀⟩ := exists_mem_support hx
  refine ⟨fun z₁ z₂ h => ?_, fun s => ?_⟩
  · have := congrArg (fun t => ((t.1 (pt hi₀) : F.sub (pt hi₀).1) : E)) h
    exact Subtype.ext this
  · have hs := LinearMap.mem_ker.mp s.2
    have hz : (s.1 (pt hi₀) : E) ∈ F.secs := by
      refine Submodule.mem_iInf _ |>.mpr fun I => ?_
      obtain ⟨i, hi⟩ := I.2.1
      have hsup : i ∈ support x := I.2.2 hi
      rw [Submodule.restrictScalars_mem, cocycle_coe_eq F hs (pt hi₀) (pt hsup)]
      exact F.mono _ I (Finset.singleton_subset_iff.mpr hi) _ (s.1 (pt hsup)).2
    refine ⟨⟨_, hz⟩, Subtype.ext (funext fun K => Subtype.ext ?_)⟩
    exact cocycle_coe_eq F hs (pt hi₀) K
end GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
