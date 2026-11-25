-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.det_one_add_smul_single_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:45:26.778533+00:00
-- url     : https://prove2.me/submissions/dea98dff-d571-4354-acea-a02089cae039

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (i : Fin n) (s : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + s • Matrix.single i i 1).det = 1 + s := by
  have h : (1 : Matrix (Fin n) (Fin n) ℂ) + s • Matrix.single i i 1 =
      Matrix.diagonal (fun j => if j = i then 1 + s else 1) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hai : a = i
      · subst hai
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, hai, Ne.symm hai]
    · have hn : ¬ (i = a ∧ i = b) := fun h => hab (h.1.symm.trans h.2)
      simp [Matrix.single_apply, hn, hab, Matrix.one_apply_ne hab]
  rw [h, Matrix.det_diagonal]
  simp
end PositivityTheory.Rg.Sw.LVs.II
