-- Prove2me | solution 1 for PositivityTheory.RgUd.T2.HaarDistr.exists_openSubgroup_char_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:40.187414+00:00
-- url     : https://prove2.me/submissions/feff4209-ec95-438d-8b81-8498881e8a67

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_PowNear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Theorems.Thm_GroundTheory_Automorphic_exists_openSubgroup_isCompact_subset
import Theorems.Thm_PositivityTheory_RgUd_T2_eq_one_of_pow_near


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob GroundTheory.Automorphic
open scoped Pointwise
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T2 PositivityTheory.RgUd.T2.HaarDistr
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
namespace PositivityTheory.RgUd.T2.HaarDistr
theorem _root_.solution (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    ∃ K : OpenSubgroup G, ∀ k ∈ K, (χ k : ℂ) = 1 := by
  have hU : IsOpen {g : G | ‖(χ g : ℂ) - 1‖ < 1 / 2} :=
    isOpen_lt (by fun_prop) continuous_const
  have h1 : (1 : G) ∈ {g : G | ‖(χ g : ℂ) - 1‖ < 1 / 2} := by simp
  obtain ⟨K, -, hKU⟩ := exists_openSubgroup_isCompact_subset (hU.mem_nhds h1)
  refine ⟨K, fun k hk => PositivityTheory.RgUd.T2.eq_one_of_pow_near fun n => ?_⟩
  have h2 : k ^ n ∈ K := pow_mem hk n
  have h3 := hKU h2
  simp only [Set.mem_setOf_eq, map_pow, Units.val_pow_eq_pow_val] at h3
  exact h3.le
end PositivityTheory.RgUd.T2.HaarDistr
