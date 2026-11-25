-- Prove2me | solution 1 for PositivityTheory.CW.EigenspaceOrthogonality.Lsym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:05.17548+00:00
-- url     : https://prove2.me/submissions/25ba525f-a18c-4df9-a530-552ad673517b

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigenspacesOrthogonalOfCalculus
import Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_key
import Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_beta_sum_left
import Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_beta_sum_right

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
open PositivityTheory.CW.EigenspaceOrthogonality
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {A : Module.End ℂ V}
namespace PositivityTheory.CW.EigenspaceOrthogonality
theorem _root_.solution (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z)) (v w : V) :
    beta ε E A (casimirK ε E v) w = beta ε E A v (casimirK ε E w) := by
  simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, beta_sum_left, beta_sum_right]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.mp hb).2
  rw [key hgl huni hA hab.symm, key hgl huni hA hab]
end PositivityTheory.CW.EigenspaceOrthogonality
