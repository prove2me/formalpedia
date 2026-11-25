-- Prove2me | solution 1 for PositivityTheory.CW.SecondMomentAlgebra.reEig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:27:02.065355+00:00
-- url     : https://prove2.me/submissions/cfebe405-c9f1-4e79-abb9-8b1a910c5607

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MatrixActionSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.SecondMomentAlgebra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.SecondMomentAlgebra
theorem _root_.solution (v : V) (μ : ℝ) : (inner ℂ v ((μ:ℂ) • v)).re = μ * ‖v‖ ^ 2 := by
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_re, pow_two]
end PositivityTheory.CW.SecondMomentAlgebra
