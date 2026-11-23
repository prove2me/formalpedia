-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.inG_one_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:15.859862+00:00
-- url     : https://prove2.me/submissions/9a115751-f123-4a60-b36c-59970601f189

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
theorem _root_.solution (P : M2 n) (h1 : Pᴴ * JJ n + JJ n * P = 0) (h2 : Pᴴ * JJ n * P = 0) (t : ℝ) :
    InG ((1 : M2 n) + t • P) := by
  unfold InG
  have key : ((1 : M2 n) + t • P)ᴴ * JJ n * (1 + t • P)
      = JJ n + t • (Pᴴ * JJ n + JJ n * P) + (t * t) • (Pᴴ * JJ n * P) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, star_trivial]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
      smul_smul, Matrix.mul_assoc]
    abel
  rw [key, h1, h2]
  simp
end PositivityTheory.Rg.Sw.LVs.II
