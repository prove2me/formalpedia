-- Prove2me | solution 1 for PositivityTheory.CW.EigenspaceOrthogonality.s1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:24:50.724686+00:00
-- url     : https://prove2.me/submissions/161ef4f2-7c66-45af-a01a-83ad062ba0a9

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigenspacesOrthogonalOfCalculus

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
theorem _root_.solution (g : Fin n → Fin n → ℂ) (c : Fin n) :
    (∑ a, ∑ b, if ε a ≠ ε b then (if c = a then g a b else 0) else 0) =
      ∑ b, if ε c ≠ ε b then g c b else 0 := by
  rw [Finset.sum_eq_single c]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp
  · intro a _ hac
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm hac]
  · simp
end PositivityTheory.CW.EigenspaceOrthogonality
