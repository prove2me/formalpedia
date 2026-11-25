-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.one_add_smul_single_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:45:10.631716+00:00
-- url     : https://prove2.me/submissions/97b7c9a1-c36d-407d-a121-d2e86a635e64

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
theorem _root_.solution (i : Fin n) (u v : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + u • Matrix.single i i 1) * (1 + v • Matrix.single i i 1) =
      1 + (u + v + u * v) • Matrix.single i i 1 := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
    Matrix.single_mul_single_same, add_smul]
  simp only [mul_comm v u]
  abel
end PositivityTheory.Rg.Sw.LVs.II
