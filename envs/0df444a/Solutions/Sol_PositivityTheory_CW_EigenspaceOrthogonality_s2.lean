-- Prove2me | solution 1 for PositivityTheory.CW.EigenspaceOrthogonality.s2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:33.31428+00:00
-- url     : https://prove2.me/submissions/0445ea11-cc4f-44f2-9a4e-e253fa137b24

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
theorem _root_.solution (g : Fin n → Fin n → ℂ) (d : Fin n) :
    (∑ a, ∑ b, if ε a ≠ ε b then (if b = d then g a b else 0) else 0) =
      ∑ a, if ε a ≠ ε d then g a d else 0 := by
  rw [Finset.sum_comm, Finset.sum_eq_single d]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp
  · intro b _ hbd
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [hbd]
  · simp
end PositivityTheory.CW.EigenspaceOrthogonality
