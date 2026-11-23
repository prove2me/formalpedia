-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.contDiff_det_one_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:34.651111+00:00
-- url     : https://prove2.me/submissions/aec83e73-c197-4687-b426-8d170eef1fd7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual

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
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (M : Matrix ι ι ℂ) {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun S : Matrix ι ι ℂ => (1 + M * S).det) := by
  have hent : ∀ a b : ι, ContDiff ℂ k (fun S : Matrix ι ι ℂ => (1 + M * S) a b) := by
    intro a b
    have e : (fun S : Matrix ι ι ℂ => (1 + M * S) a b) =
        fun S => (1 : Matrix ι ι ℂ) a b + ∑ c, M a c * S c b := by
      funext S; simp [Matrix.add_apply, Matrix.mul_apply]
    rw [e]
    exact contDiff_const.add (ContDiff.sum fun c _ => contDiff_const.mul (contDiff_apply_apply ℂ ℂ c b))
  simp only [Matrix.det_apply]
  exact ContDiff.sum fun σ _ => (contDiff_prod fun i _ => hent _ _).const_smul _
end PositivityTheory.Rg.Sw.LVs
