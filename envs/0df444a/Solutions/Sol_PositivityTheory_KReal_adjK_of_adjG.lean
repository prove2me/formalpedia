-- Prove2me | solution 1 for PositivityTheory.KReal.adjK_of_adjG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:29.932888+00:00
-- url     : https://prove2.me/submissions/7dbe78f9-048a-470c-ad4a-2017bb882413

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc

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
open PositivityTheory PositivityTheory.KReal
variable {r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] {act : Mat r s →ₗ[ℂ] Module.End ℂ A} (h : AdjG act) : AdjK (units act) := by
  intro a b hab u v
  have := h a b u v
  rw [epsB, if_pos hab, one_mul] at this
  exact this
end PositivityTheory.KReal
