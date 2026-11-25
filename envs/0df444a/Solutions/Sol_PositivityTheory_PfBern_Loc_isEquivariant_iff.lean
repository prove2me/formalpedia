-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.isEquivariant_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:39:13.503095+00:00
-- url     : https://prove2.me/submissions/2173c645-657b-491e-8ee5-06c40157154b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariant

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
namespace PositivityTheory.PfBern.Loc
theorem _root_.solution {ι : Type*} (e : ι → X ≃ₜ X) (χ : ι → ℂ) (D : Distr X) :
    IsEquivariant e χ D ↔ ∀ w ∈ relSpanH e χ, D w = 0 := by
  constructor
  · intro hD w hw
    have hle : relSpanH e χ ≤ LinearMap.ker D := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨i, f⟩, rfl⟩
      simp [hD i f]
    exact hle hw
  · intro hD i f
    have := hD _ (Submodule.subset_span ⟨(i, f), rfl⟩)
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
    exact this
end PositivityTheory.PfBern.Loc
