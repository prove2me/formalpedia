-- Prove2me | solution 1 for PositivityTheory.CW.FunctionalCalculusInner.fc_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:47.204691+00:00
-- url     : https://prove2.me/submissions/ac341935-46f6-4802-be8c-13dee2a06738

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusOfBasic

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
open PositivityTheory.CW.FunctionalCalculusInner
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
namespace PositivityTheory.CW.FunctionalCalculusInner
theorem _root_.solution (b : Module.Basis ι ℂ V) (μ : ι → ℝ) (φ : ℝ → ℝ) (i : ι) :
    fc b μ φ (b i) = ((φ (μ i) : ℝ) : ℂ) • b i := by
  unfold fc
  exact b.constr_basis ℂ _ i
end PositivityTheory.CW.FunctionalCalculusInner
