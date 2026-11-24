-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.triv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:27:03.478992+00:00
-- url     : https://prove2.me/submissions/8837f056-dc46-425c-834a-6a659ac82137

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
theorem _root_.solution (q : X × H) :
    triv hp σ hpc q = (σ.s (p q.1) * q.2, fibSmul hp q.2⁻¹ (zpart hp σ q.1)) := rfl
end PositivityTheory.PfBern.Frob
