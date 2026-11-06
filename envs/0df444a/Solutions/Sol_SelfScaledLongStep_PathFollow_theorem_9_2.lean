-- Prove2me | solution 1 for SelfScaledLongStep.PathFollow.theorem_9_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T13:15:21.922197+00:00
-- url     : https://prove2.me/submissions/15b6a547-8b63-43bb-8ddc-83267708f010
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PathFollow_Defs
import Theorems.Thm_SelfScaledLongStep_PathFollow_theorem_4_3
import Theorems.Thm_SelfScaledLongStep_PathFollow_proposition_6_3
import Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_4_1
import Theorems.Thm_SelfScaledIPM_FuncProx_proposition_3_5

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep
open SelfScaledLongStep.PathFollow

theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A) (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hD : ∃ (y : EuclideanSpace ℝ (Fin m)) (s : EuclideanSpace ℝ (Fin n)), IsDualStrict K A c y s)
    (τ : ℝ) (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin n)) (hx : IsPrimalStrict K A b x)
    (y : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n))
    (hp : IsNewtonDir F A c τ x y p) (hπ : lnorm F x p < 1) :
    IsPrimalStrict K A b (x - p) ∧
      ∀ (y' : EuclideanSpace ℝ (Fin m)) (p' : EuclideanSpace ℝ (Fin n)),
        IsNewtonDir F A c τ (x - p) y' p' →
          lnorm F (x - p) p' ≤ absn K x p * lnorm F x p ∧
            absn K x p * lnorm F x p ≤ (lnorm F x p) ^ 2 := by
  obtain ⟨hxK, hAx⟩ := hx
  have h35 := (SelfScaledIPM.FuncProx.proposition_3_5 K hK F ν hν hF).1 x hxK p
  have hl0 : 0 ≤ lnorm F x p := Real.sqrt_nonneg _
  have hσ : sigma K x p ≤ absn K x p := le_max_left _ _
  have h41 := SelfScaledLongStep.PrimalDual.theorem_4_1 K hK F ν hν hF x p hxK 1 zero_le_one
    (by linarith [h35.1])
  rw [one_smul] at h41
  have hxp : x - p ∈ interior K := h41.1
  have hAxp : A (x - p) = b := by rw [map_sub, hp.1, sub_zero, hAx]
  refine ⟨⟨hxp, hAxp⟩, ?_⟩
  intro y' p' hp'
  refine ⟨?_, ?_⟩
  · have h63 := (proposition_6_3 K hK F ν hν hF A hA (x - p) _ hxp y' p' hp').1 y
    have hid : τ • c + gradient F (x - p) - ContinuousLinearMap.adjoint A y =
        gradient F (x - p) - gradient F x - hess F x (x - p - x) := by
      have e : τ • c = ContinuousLinearMap.adjoint A y + hess F x p - gradient F x := by
        rw [hp.2]; abel
      rw [e, show x - p - x = -p by abel, map_neg]
      abel
    rw [hid] at h63
    have h43 := theorem_4_3 K hK F ν hν hF x (x - p) hxK hxp
    have e1 : x - p - x = -p := by abel
    have habs : absn K x (-p) = absn K x p := by
      unfold absn; rw [neg_neg, max_comm]
    have hln : lnorm F x (-p) = lnorm F x p := by
      unfold lnorm; rw [map_neg, inner_neg_neg]
    rw [e1, habs, hln] at h43
    rw [e1] at h63
    exact h63.trans h43
  · rw [sq]
    exact mul_le_mul_of_nonneg_right h35.1 hl0
