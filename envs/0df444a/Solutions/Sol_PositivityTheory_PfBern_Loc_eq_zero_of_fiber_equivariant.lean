-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.eq_zero_of_fiber_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:50.220429+00:00
-- url     : https://prove2.me/submissions/77121455-b7fc-42ce-89f9-cc45a2ebe353

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariant
import Theorems.Thm_PositivityTheory_PfBern_Loc_eq_zero_of_fiber
import Theorems.Thm_PositivityTheory_PfBern_Loc_isEquivariant_iff
import Theorems.Thm_PositivityTheory_PfBern_Loc_fiberStable_relSpanH

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
theorem _root_.solution {ι : Type*} {p : X → Y} (hp : Continuous p)
    (e : ι → X ≃ₜ X) (χ : ι → ℂ) (he : ∀ i x, p (e i x) = p x)
    (hfib : ∀ (y : Y) (D : Distr X), IsEquivariant e χ D → SupportedIn D (p ⁻¹' {y}) → D = 0)
    (D : Distr X) (hD : IsEquivariant e χ D) : D = 0 :=
  eq_zero_of_fiber hp (relSpanH e χ) (fiberStable_relSpanH e χ he)
    (fun y D' hD' hsupp => hfib y D' ((isEquivariant_iff e χ D').2 hD') hsupp)
    D ((isEquivariant_iff e χ D).1 hD)
end PositivityTheory.PfBern.Loc
