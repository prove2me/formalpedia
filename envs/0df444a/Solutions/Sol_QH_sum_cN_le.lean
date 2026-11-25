-- Prove2me | solution 1 for QH.sum_cN_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:15.222424+00:00
-- url     : https://prove2.me/submissions/34869c0b-76bc-4fbc-98d3-a4e9b6e4e764

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailMertens
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_SumCNLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_mertens


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ y Z : ℝ, 0 ≤ y → 2 ≤ Z → ∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n ≤ C * y * Real.log Z := by
  obtain ⟨C, hC, hM⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_mertens
  refine ⟨C + 1, by linarith, fun y Z hy hZ => ?_⟩
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  calc ∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n
        ≤ ∑ n ∈ Icc 1 ⌊Z⌋₊, y * (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
          simp only [cN]
          calc ArithmeticFunction.vonMangoldt n * min 1 (y / n)
              ≤ ArithmeticFunction.vonMangoldt n * (y / n) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) hΛ
            _ = y * (ArithmeticFunction.vonMangoldt n / n) := by ring
    _ = y * ∑ n ∈ Icc 1 ⌊Z⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
          rw [Finset.mul_sum]
    _ ≤ y * (C * Real.log Z) := mul_le_mul_of_nonneg_left (hM Z hZ) hy
    _ ≤ (C + 1) * y * Real.log Z := by nlinarith [mul_nonneg hy hlog]
end QH
