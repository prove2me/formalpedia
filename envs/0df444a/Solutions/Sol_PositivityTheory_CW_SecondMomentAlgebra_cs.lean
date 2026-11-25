-- Prove2me | solution 1 for PositivityTheory.CW.SecondMomentAlgebra.cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:59.329424+00:00
-- url     : https://prove2.me/submissions/bc6d7717-f91d-49d4-b438-0edd3383b7ca

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
theorem _root_.solution {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ c, ∑ d, f c d) ^ 2 ≤ ((n:ℝ) * n) * ∑ c, ∑ d, f c d ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n × Fin n))) (f := fun p => f p.1 p.2)
  simpa [Fintype.sum_prod_type', Fintype.sum_prod_type, Finset.card_univ] using h
end PositivityTheory.CW.SecondMomentAlgebra
