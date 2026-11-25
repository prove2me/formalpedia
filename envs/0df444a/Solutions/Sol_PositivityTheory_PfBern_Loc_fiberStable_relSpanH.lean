-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.fiberStable_relSpanH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:27.357774+00:00
-- url     : https://prove2.me/submissions/9da49804-48ac-4092-be7b-4bc0fab15d0b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariant
import Theorems.Thm_PositivityTheory_PfBern_Loc_mulInd_compHomeoL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Loc
variable {X : Type*} [TopologicalSpace X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y]
omit [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
namespace PositivityTheory.PfBern.Loc
theorem _root_.solution {ι : Type*} {p : X → Y} (e : ι → X ≃ₜ X) (χ : ι → ℂ)
    (he : ∀ i x, p (e i x) = p x) : FiberStable p (relSpanH e χ) := by
  intro V _ hpV w hw
  have hle : relSpanH e χ ≤ (relSpanH e χ).comap (mulInd (p ⁻¹' V) hpV) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨i, f⟩, rfl⟩
    show mulInd (p ⁻¹' V) hpV (compHomeoL (e i) f - χ i • f) ∈ relSpanH e χ
    rw [map_sub, map_smul, mulInd_compHomeoL (e i) (he i)]
    exact Submodule.subset_span ⟨(i, mulInd (p ⁻¹' V) hpV f), rfl⟩
  exact hle hw
end PositivityTheory.PfBern.Loc
