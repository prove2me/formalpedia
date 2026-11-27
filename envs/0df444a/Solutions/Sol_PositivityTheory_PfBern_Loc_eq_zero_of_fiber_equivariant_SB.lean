-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.eq_zero_of_fiber_equivariant_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:34:11.196958+00:00
-- url     : https://prove2.me/submissions/72d9b79a-e228-4dc6-9aae-5ba91b3b4973

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariantSB
import Theorems.Thm_PositivityTheory_PfBern_Loc_eq_zero_of_fiber_equivariant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Loc
namespace PositivityTheory.PfBern.Loc
theorem _root_.solution {X : Type*} [TopologicalSpace X] {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    {ι : Type*} {p : X → Y} (hp : Continuous p)
    (e : ι → X ≃ₜ X) (χ : ι → ℂ) (he : ∀ i x, p (e i x) = p x)
    (hfib : ∀ (y : Y) (D : Module.Dual ℂ (GlobalTheory.SplitWeil.SB X)),
      (∀ (i : ι) (f : GlobalTheory.SplitWeil.SB X),
        D ⟨fun x => (f : X → ℂ) (e i x), f.2.1.comp_continuous (e i).continuous,
          f.2.2.comp_homeomorph (e i)⟩ = χ i * D f) →
      (∀ f : GlobalTheory.SplitWeil.SB X, Function.support (f : X → ℂ) ⊆ (p ⁻¹' {y})ᶜ → D f = 0) → D = 0)
    (D : Module.Dual ℂ (GlobalTheory.SplitWeil.SB X))
    (hD : ∀ (i : ι) (f : GlobalTheory.SplitWeil.SB X),
        D ⟨fun x => (f : X → ℂ) (e i x), f.2.1.comp_continuous (e i).continuous,
          f.2.2.comp_homeomorph (e i)⟩ = χ i * D f) : D = 0 :=
  eq_zero_of_fiber_equivariant (D := D) hp e χ he (fun y D' hD' hs => hfib y D' hD' hs) hD
end PositivityTheory.PfBern.Loc
