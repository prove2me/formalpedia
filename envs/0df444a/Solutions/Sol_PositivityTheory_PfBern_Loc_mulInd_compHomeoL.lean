-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.mulInd_compHomeoL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:39:15.187726+00:00
-- url     : https://prove2.me/submissions/4e9f87d2-7fa7-4998-bdbd-bf5bfd8fe488

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
omit [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
namespace PositivityTheory.PfBern.Loc
theorem _root_.solution {p : X → Y} (e : X ≃ₜ X) (he : ∀ x, p (e x) = p x) (V : Set Y)
    (hpV : IsClopen (p ⁻¹' V)) (f : SC X) :
    mulInd (p ⁻¹' V) hpV (compHomeoL e f) = compHomeoL e (mulInd (p ⁻¹' V) hpV f) := by
  refine Subtype.ext <| funext fun x => ?_
  simp only [coe_mulInd, coe_compHomeoL, Function.comp_apply]
  congr 1
  by_cases hx : p x ∈ V <;> simp [hx, he]
end PositivityTheory.PfBern.Loc
