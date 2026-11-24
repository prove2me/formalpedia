-- Prove2me | solution 1 for PositivityTheory.KReal.quadT_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:48.012337+00:00
-- url     : https://prove2.me/submissions/2c180dc8-4668-4ce1-941f-c689c914b5e0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PositivityTheory PositivityTheory.KReal
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Ring E] [Algebra ℂ E]
namespace PositivityTheory.KReal
theorem _root_.solution (R L : ι → E)
    (hLR : ∀ a b, L a * R b = R b * L a + if a = b then 1 else 0) (A B : Matrix ι ι ℂ) :
    quadT R L A * quadT R L B = quartT R L A B + quadT R L (A * B) := by
  have key : ∀ i j k l, (A i j • (R i * L j)) * (B k l • (R k * L l)) =
      (A i j * B k l) • (R i * R k * (L j * L l)) +
        if j = k then (A i j * B k l) • (R i * L l) else 0 := by
    intro i j k l
    have h1 : R i * L j * (R k * L l) = R i * (L j * R k) * L l := by simp only [mul_assoc]
    rw [smul_mul_smul_comm, h1, hLR]
    split_ifs with h
    · simp only [mul_add, add_mul, mul_one, smul_add, mul_assoc]
    · simp only [add_zero, mul_assoc]
  have h2 : quadT R L (A * B) =
      ∑ i, ∑ j, ∑ k, ∑ l, if j = k then (A i j * B k l) • (R i * L l) else 0 := by
    unfold quadT
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp
  rw [h2]
  unfold quadT quartT
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => key i j k l
end PositivityTheory.KReal
