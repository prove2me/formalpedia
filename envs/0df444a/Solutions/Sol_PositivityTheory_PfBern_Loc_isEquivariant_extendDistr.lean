-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.isEquivariant_extendDistr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:22:12.424015+00:00
-- url     : https://prove2.me/submissions/39b47279-a1b2-4df3-bb52-133d279854c9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariant
import Theorems.Thm_PositivityTheory_PfBern_Loc_extendDistr_apply
import Theorems.Thm_PositivityTheory_PfBern_Loc_restr_compHomeoL

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
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y]
omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y]
  [LocallyCompactSpace Y]
namespace PositivityTheory.PfBern.Loc
theorem _root_.solution {ι : Type*} {p : X → Y} (hp : Continuous p)
    (e : ι → X ≃ₜ X) (χ : ι → ℂ) (he : ∀ i x, p (e i x) = p x) (y : Y)
    (D' : Distr (p ⁻¹' {y})) (hD' : IsEquivariant (fun i => fiberHomeo (e i) (he i) y) χ D') :
    IsEquivariant e χ (extendDistr (isClosed_singleton.preimage hp) D') := by
  intro i f
  rw [extendDistr_apply, extendDistr_apply, restr_compHomeoL _ (e i)]
  exact hD' i _
end PositivityTheory.PfBern.Loc
