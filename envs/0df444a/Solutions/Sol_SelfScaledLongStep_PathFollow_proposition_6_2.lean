-- Prove2me | solution 1 for SelfScaledLongStep.PathFollow.proposition_6_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:49:44.656682+00:00
-- url     : https://prove2.me/submissions/16a54f90-0e29-4385-8cff-c8e6f3bbed90

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PathFollow_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

open SelfScaledLongStep.PathFollow in
theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    {m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : Function.Surjective A)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : w ∈ interior K)
    (y : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n))
    (hp : SelfScaledLongStep.PrimalDual.IsProjection F A w u y p) :
    (lnorm F w p) ^ 2 = ⟪u, p⟫_ℝ := by
  have hnn : 0 ≤ ⟪hess F w p, p⟫_ℝ := by
    by_cases h0 : p = 0
    · subst h0
      simp
    · exact le_of_lt (hF.1.2.2.2.2 w hw p h0)
  unfold lnorm
  rw [Real.sq_sqrt hnn, ← hp.2, inner_add_left, ContinuousLinearMap.adjoint_inner_left, hp.1,
    inner_zero_right, zero_add]
