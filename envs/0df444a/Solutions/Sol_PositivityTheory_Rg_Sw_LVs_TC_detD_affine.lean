-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.detD_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:44.793748+00:00
-- url     : https://prove2.me/submissions/4e94a521-3571-4dbf-9abf-81057e923d3f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlock
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (hA : IterAffine) {F : M2 n → ℂ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω)
    {g : M2 n} (hg : g ∈ Ω) (L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n) :
    detD (fun t => F (g + L t)) = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => L (single ((Fintype.equivFin (Fin n)).symm i)
        (σ ((Fintype.equivFin (Fin n)).symm i)) 1)) := by
  unfold detD
  refine Finset.sum_congr rfl fun σ _ => ?_
  erw [hA (M2 n) (Matrix (Fin n) (Fin n) ℂ) F Ω hΩ hF g hg L]
  rfl
end PositivityTheory.Rg.Sw.LVs.TC
