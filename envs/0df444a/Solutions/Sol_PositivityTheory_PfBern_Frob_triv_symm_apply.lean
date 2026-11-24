-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.triv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:27:05.580183+00:00
-- url     : https://prove2.me/submissions/7541c92b-f3fb-4bc7-a1d5-e5bf0690fc2a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  {X : Type} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H}
variable (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)
variable (hpc : Continuous p)
namespace PositivityTheory.PfBern.Frob
theorem _root_.solution (r : G × Fib p) :
    (triv hp σ hpc).symm r = (r.1 • r.2.1, ⟨(σ.s (r.1 : G ⧸ H))⁻¹ * r.1, σ.inv_mul_mem r.1⟩) := rfl
end PositivityTheory.PfBern.Frob
