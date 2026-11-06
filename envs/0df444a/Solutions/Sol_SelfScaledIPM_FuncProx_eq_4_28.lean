-- Prove2me | solution 1 for SelfScaledIPM.FuncProx.eq_4_28
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T03:26:20.15693+00:00
-- url     : https://prove2.me/submissions/d292081b-8436-4465-9e62-284d1a664382
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures
import Theorems.Thm_SelfScaledIPM_FuncProx_theorem_4_2_global

open scoped InnerProductSpace
open SelfScaledIPM.FuncProx

theorem solution
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    (x s : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    (3 / 4 : ℝ) * gammaInf K F ν x s - 1 / 4 ≤ gammaG K F ν x s := by
  obtain ⟨-, -, ⟨h1, h2⟩, -, -, -⟩ := theorem_4_2_global K hK F ν hν hF x s hx hs
  have hνpos : (0 : ℝ) < ν := by linarith
  have hge : 0 ≤ 1 + gammaInf K F ν x s := by
    unfold gammaInf
    have hμ : 0 ≤ SelfScaledIPM.ShortStep.mu ν x s := by
      unfold SelfScaledIPM.ShortStep.mu
      apply div_nonneg _ hνpos.le
      rw [real_inner_comm]; exact (interior_subset hs) x (interior_subset hx)
    have hσ : 0 ≤ SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) s (-gradient F x) :=
      Real.sInf_nonneg (fun b hb => hb.1)
    nlinarith [mul_nonneg hμ hσ]
  generalize gammaInf K F ν x s = g at *
  generalize gammaG K F ν x s = G at *
  rcases hge.lt_or_eq with hpos | hzero
  · rw [div_le_iff₀ hpos] at h1
    nlinarith [sq_nonneg (g - 1)]
  · have hg : g = -1 := by linarith
    rw [← hzero, div_zero] at h1
    rw [hg] at h2
    nlinarith
