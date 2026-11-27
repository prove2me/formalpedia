-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:00.80662+00:00
-- url     : https://prove2.me/submissions/e5af27fe-50e8-4524-9324-3fe97bdf02eb

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ParabolicBlockForms_UpperBlockRankOneUpdate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq
open Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
namespace PositivityTheory.SiegelWeilFormula.Act.C4.Bq
namespace NQ
theorem _root_.solution {x y : ι} {M N : Matrix ι ι R} (hM : NQ x y M) (hN : NQ x y N) : NQ x y (M * N) := by
  have e : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]; abel
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · rw [e, Matrix.add_apply, Matrix.add_apply, hM.1 k, hN.1 k, Matrix.mul_apply]
    simp only [zero_add]
    exact Finset.sum_eq_zero fun m _ => by rw [hN.1 m, mul_zero]
  · rw [e, Matrix.add_apply, Matrix.add_apply, hM.2 k l hlx hly hkx, hN.2 k l hlx hly hkx, Matrix.mul_apply]
    simp only [zero_add]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : m = x
    · subst hm; rw [hM.1 k, zero_mul]
    · rw [hN.2 m l hlx hly hm, mul_zero]
end NQ
end PositivityTheory.SiegelWeilFormula.Act.C4.Bq
