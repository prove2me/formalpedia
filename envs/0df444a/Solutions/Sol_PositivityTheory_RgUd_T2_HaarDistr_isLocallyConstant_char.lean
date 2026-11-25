-- Prove2me | solution 1 for PositivityTheory.RgUd.T2.HaarDistr.isLocallyConstant_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:02.45826+00:00
-- url     : https://prove2.me/submissions/bb2b4266-9bf8-4b48-befc-2e62dab11ce5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_PowNear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_exists_openSubgroup_char_eq_one

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
    IsLocallyConstant (fun g => (χ g : ℂ)) := by
  obtain ⟨K, hK⟩ := exists_openSubgroup_char_eq_one χ hχ
  refine (IsLocallyConstant.iff_exists_open _).2 fun g => ?_
  refine ⟨g • (K : Set G), K.isOpen.smul g, Set.mem_smul_set.2 ⟨1, K.one_mem, mul_one g⟩, ?_⟩
  rintro _ hy
  obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hy
  simp [hK k hk]
end PositivityTheory.RgUd.T2.HaarDistr
