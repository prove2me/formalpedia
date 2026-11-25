-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TBNum.netSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:43:15.601523+00:00
-- url     : https://prove2.me/submissions/0a5fce05-ad6c-4e6f-a07d-3a94c5ae2946

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ScaledBoundInequalityHypothesesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_SchwarzBallNumerics_NetSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TBNum
open ComplexConjugate
namespace PI.UnitaryGroupMassFormula.TBNum
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.NetSupSt := by
  intro ι _ f S hf hS ⟨y0, hy0⟩
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨y0⟩
  have key : Real.sqrt (Fintype.card ι) * Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ y, f y ^ 2)
      = Real.sqrt (∑ y, f y ^ 2) := by
    rw [← Real.sqrt_mul hn.le, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  have h1 : f y0 ^ 2 ≤ ∑ y, f y ^ 2 :=
    Finset.single_le_sum (f := fun y => f y ^ 2) (fun y _ => sq_nonneg (f y)) (Finset.mem_univ y0)
  have h2 : f y0 ≤ Real.sqrt (∑ y, f y ^ 2) := by
    rw [← Real.sqrt_sq (hf y0)]
    exact Real.sqrt_le_sqrt h1
  calc S ≤ 4 * f y0 := by linarith
    _ ≤ 4 * Real.sqrt (∑ y, f y ^ 2) := by linarith
    _ = _ := by rw [mul_assoc, key]
end PI.UnitaryGroupMassFormula.TBNum
