-- Prove2me | solution 1 for PositivityTheory.CW.CasimirEigenvector.comm_casimirK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:06.72811+00:00
-- url     : https://prove2.me/submissions/ce9c1133-975e-44b4-8188-8c8af44cc835

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirRealScalar

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
open PositivityTheory.CW.CasimirEigenvector
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}
namespace PositivityTheory.CW.CasimirEigenvector
theorem _root_.solution (T : Module.End ℂ V) (hT : ∀ a b, E a b * T = T * E a b) :
    casimirK ε E * T = T * casimirK ε E := by
  unfold casimirK
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_assoc, hT b a, ← mul_assoc, hT a b, mul_assoc]
end PositivityTheory.CW.CasimirEigenvector
