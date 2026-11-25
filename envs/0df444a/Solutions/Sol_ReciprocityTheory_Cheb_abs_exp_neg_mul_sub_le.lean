-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_exp_neg_mul_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:27.311318+00:00
-- url     : https://prove2.me/submissions/2ddbd059-7381-449a-b38a-dbb097f5a2eb

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {s u v L : ℝ} (hs : 1 ≤ s) (hL : 0 ≤ L) (hu : L ≤ u) (hv : L ≤ v) :
    |Real.exp (-s * u) - Real.exp (-s * v)| ≤ s * |u - v| * Real.exp (-L) := by
  have key : ∀ u v : ℝ, L ≤ u → u ≤ v →
      Real.exp (-s * u) - Real.exp (-s * v) ≤ s * (v - u) * Real.exp (-L) := by
    intro u v hu huv
    have e1 : Real.exp (-s * v) = Real.exp (-s * u) * Real.exp (-(s * (v - u))) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : 1 - Real.exp (-(s * (v - u))) ≤ s * (v - u) := by
      linarith [Real.add_one_le_exp (-(s * (v - u)))]
    have e3 : Real.exp (-s * u) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by nlinarith)
    have e4 : 0 ≤ s * (v - u) := mul_nonneg (by linarith) (by linarith)
    rw [e1]
    calc Real.exp (-s * u) - Real.exp (-s * u) * Real.exp (-(s * (v - u)))
        = Real.exp (-s * u) * (1 - Real.exp (-(s * (v - u)))) := by ring
      _ ≤ Real.exp (-L) * (s * (v - u)) :=
        mul_le_mul e3 e2 (by linarith [Real.exp_le_one_iff.mpr (by linarith : -(s * (v - u)) ≤ 0)])
          (Real.exp_pos _).le
      _ = s * (v - u) * Real.exp (-L) := by ring
  rcases le_total u v with huv | hvu
  · have h := key u v hu huv
    have hm : Real.exp (-s * v) ≤ Real.exp (-s * u) := Real.exp_le_exp.mpr (by nlinarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h := key v u hv hvu
    have hm : Real.exp (-s * u) ≤ Real.exp (-s * v) := Real.exp_le_exp.mpr (by nlinarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith
end ReciprocityTheory.Cheb
