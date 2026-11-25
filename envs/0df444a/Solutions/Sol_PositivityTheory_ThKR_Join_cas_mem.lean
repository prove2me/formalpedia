-- Prove2me | solution 1 for PositivityTheory.ThKR.Join.cas_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:07:48.87753+00:00
-- url     : https://prove2.me/submissions/5b9d9473-e45e-4421-bf7d-809a5ae1a536

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_ExistsGreatestProperInvariantSubmoduleOfSide
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Join
open PositivityTheory.KReal PositivityTheory.ThKF.Unit
variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKR.Join
theorem _root_.solution (act : Mat r s →ₗ[ℂ] Module.End ℂ M) : casK (units act) ∈ Algebra.adjoin ℂ (Set.range act) := by
  refine sum_mem fun a _ => sum_mem fun b _ => ?_
  split_ifs
  · exact mul_mem (Algebra.subset_adjoin ⟨_, rfl⟩) (Algebra.subset_adjoin ⟨_, rfl⟩)
  · exact zero_mem _
end PositivityTheory.ThKR.Join
