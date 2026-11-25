-- Prove2me | solution 1 for PositivityTheory.CW.FormEigenMonotone.beta_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:06.707931+00:00
-- url     : https://prove2.me/submissions/6948e3b9-aa5b-4ceb-a79e-f461fd063c22

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisSumOfOrthogonality

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
open PositivityTheory.CW.FormEigenMonotone
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
namespace PositivityTheory.CW.FormEigenMonotone
theorem _root_.solution (A B : Module.End ℂ V) (v w : V) :
    beta ε E (A + B) v w = beta ε E A v w + beta ε E B v w := by
  simp only [beta, LinearMap.add_apply, inner_add_right, Finset.sum_add_distrib]
end PositivityTheory.CW.FormEigenMonotone
