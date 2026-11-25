-- Prove2me | solution 1 for PositivityTheory.CW.EigenspaceOrthogonality.comm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:24:45.479691+00:00
-- url     : https://prove2.me/submissions/12e917ab-cde3-4767-8ca6-4c7af7885bec

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
theorem _root_.solution (hgl : IsGlRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) +
      ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have h := congrArg (fun T : Module.End ℂ V => T x) (hgl a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [← sub_eq_iff_eq_add', h]
  split_ifs <;> simp
end PositivityTheory.CW.EigenspaceOrthogonality
