-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.eq_zero_of_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:32.125891+00:00
-- url     : https://prove2.me/submissions/f5fa17d8-361a-4417-80df-9927c6185bd7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariant
import Theorems.Thm_PositivityTheory_PfBern_Loc_eq_top_of_fiber

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
theorem _root_.solution {p : X → Y} (hp : Continuous p) (W : Submodule ℂ (SC X))
    (hW : FiberStable p W)
    (hfib : ∀ (y : Y) (D : Distr X), (∀ w ∈ W, D w = 0) → SupportedIn D (p ⁻¹' {y}) → D = 0)
    (D : Distr X) (hD : ∀ w ∈ W, D w = 0) : D = 0 := by
  have htop := eq_top_of_fiber hp W hW hfib
  ext f
  rw [LinearMap.zero_apply]
  exact hD f (htop ▸ Submodule.mem_top)
end PositivityTheory.PfBern.Loc
