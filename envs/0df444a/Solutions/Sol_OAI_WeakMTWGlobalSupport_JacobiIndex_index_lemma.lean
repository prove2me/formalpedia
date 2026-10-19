-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.JacobiIndex.index_lemma
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T03:09:30.202736+00:00
-- url     : https://prove2.me/submissions/a2c6956f-11a9-4b37-9a7f-8e5011170a73

import Mathlib
import Definitions.Def_OAIQWMTW001

section
-- module Solutions.OAIQW_WeakMTW.Support_FirstCutSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology

namespace JacobiIndex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem indexForm_symm {R : ℝ → E →L[ℝ] E}
    (hR : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v)) (U V : ℝ → E) :
    indexForm R U V = indexForm R V U := by
  unfold indexForm
  congr 1
  funext t
  simp only [integrand]
  rw [real_inner_comm (deriv U t) (deriv V t), hR t (U t) (V t),
    real_inner_comm (U t) (R t (V t))]

theorem continuous_integrand {R : ℝ → E →L[ℝ] E} {U V : ℝ → E}
    (hR : Continuous R) (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V) :
    Continuous (integrand R U V) :=
  (hU.continuous_deriv_one.inner hV.continuous_deriv_one).sub
    ((hR.clm_apply hU.continuous).inner hV.continuous)

theorem indexForm_jacobi {R : ℝ → E →L[ℝ] E} {U K : ℝ → E}
    (hR : Continuous R)
    (hsymm : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v))
    (hU : ContDiff ℝ 1 U) (hK : ContDiff ℝ 2 K)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv K) t = -(R t (K t))) :
    indexForm R U K = inner ℝ (U 1) (deriv K 1) - inner ℝ (U 0) (deriv K 0) := by
  have hK' : ContDiff ℝ 1 (deriv K) := hK.deriv'
  unfold indexForm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => inner ℝ (U t) (deriv K t))
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hd := HasDerivAt.inner ℝ
      ((hU.differentiable (by norm_num)) t).hasDerivAt
      ((hK'.differentiable (by norm_num)) t).hasDerivAt
    have heq : integrand R U K t =
        inner ℝ (U t) (deriv (deriv K) t) + inner ℝ (deriv U t) (deriv K t) := by
      simp only [integrand, hjac t ht', inner_neg_right, ← hsymm]
      ring
    rw [heq]
    exact hd
  · exact (continuous_integrand hR hU (hK.of_le (by norm_num))).intervalIntegrable (μ := volume) 0 1

theorem indexForm_trial_expansion {R : ℝ → E →L[ℝ] E} {U K : ℝ → E}
    (hR : Continuous R)
    (hsymm : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v))
    (hU : ContDiff ℝ 1 U) (hK : ContDiff ℝ 1 K) (a : ℝ) :
    indexForm R (U + a • K) (U + a • K) =
      indexForm R U U + 2 * a * indexForm R U K + a ^ 2 * indexForm R K K := by
  have hid : integrand R (U + a • K) (U + a • K) = fun t =>
      integrand R U U t + 2 * a * integrand R U K t + a ^ 2 * integrand R K K t := by
    funext t
    have hUt := (hU.differentiable (by norm_num)) t
    have hKt := (hK.differentiable (by norm_num)) t
    simp only [integrand, deriv_add hUt (hKt.const_smul a), deriv_const_smul a hKt,
      Pi.add_apply, Pi.smul_apply, map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, inner_smul_right]
    rw [real_inner_comm (deriv K t) (deriv U t), hsymm t (K t) (U t),
      real_inner_comm (K t) (R t (U t))]
    ring
  unfold indexForm
  rw [hid]
  have hUU := (continuous_integrand hR hU hU).intervalIntegrable (μ := volume) 0 1
  have hUK := (continuous_integrand hR hU hK).intervalIntegrable (μ := volume) 0 1
  have hKK := (continuous_integrand hR hK hK).intervalIntegrable (μ := volume) 0 1
  rw [intervalIntegral.integral_add (hUU.add (hUK.const_mul (2 * a)))
      (hKK.const_mul (a ^ 2)), intervalIntegral.integral_add hUU (hUK.const_mul (2 * a)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem jacobi_minimizes_index_proof {R : ℝ → E →L[ℝ] E} {Y X : ℝ → E}
    (hR : Continuous R)
    (hsymm : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v))
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 2 Y)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv Y) t = -(R t (Y t)))
    (hstart : X 0 = Y 0) (hend : X 1 = Y 1)
    (hmin : ∀ Z : ℝ → E, ContDiff ℝ 1 Z → Z 0 = 0 → Z 1 = 0 →
      0 ≤ indexForm R Z Z) :
    indexForm R Y Y ≤ indexForm R X X := by
  let Z := X - Y
  have hZ : ContDiff ℝ 1 Z := hX.sub (hY.of_le (by norm_num))
  have hZ0 : Z 0 = 0 := by simp [Z, hstart]
  have hZ1 : Z 1 = 0 := by simp [Z, hend]
  have hcross := indexForm_jacobi hR hsymm hZ hY hjac
  rw [hZ0, hZ1, inner_zero_left, inner_zero_left, sub_self,
    indexForm_symm hsymm Z Y] at hcross
  have hexp := indexForm_trial_expansion hR hsymm (hY.of_le (by norm_num)) hZ (1 : ℝ)
  have hsum : Y + (1 : ℝ) • Z = X := by simp [Z]
  rw [hsum, hcross] at hexp
  have hnonneg := hmin Z hZ hZ0 hZ1
  linarith

theorem index_lemma_oai {R : ℝ → E →L[ℝ] E} {Y X : ℝ → E}
    (hR : Continuous R)
    (hsymm : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v))
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 2 Y)
    (hjac : ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv (deriv Y) t = -(R t (Y t)))
    (hstart : X 0 = Y 0) (hend : X 1 = Y 1)
    (hmin : ∀ Z : ℝ → E, ContDiff ℝ 1 Z → Z 0 = 0 → Z 1 = 0 →
      0 ≤ ∫ t in (0 : ℝ)..1, (inner ℝ (deriv Z t) (deriv Z t) - inner ℝ (R t (Z t)) (Z t))) :
    (∫ t in (0 : ℝ)..1, (inner ℝ (deriv Y t) (deriv Y t) - inner ℝ (R t (Y t)) (Y t))) ≤
      ∫ t in (0 : ℝ)..1, (inner ℝ (deriv X t) (deriv X t) - inner ℝ (R t (X t)) (X t)) :=
  jacobi_minimizes_index_proof hR hsymm hX hY hjac hstart hend hmin

end JacobiIndex

open Set Filter MeasureTheory
open scoped Topology

end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWGlobalSupport.JacobiIndex.index_lemma_oai.{u_1} := @OAI.WeakMTWGlobalSupport.JacobiIndex.index_lemma_oai.{u_1}
