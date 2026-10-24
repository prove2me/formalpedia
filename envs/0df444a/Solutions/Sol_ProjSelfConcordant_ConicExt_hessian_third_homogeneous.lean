-- Prove2me | solution 1 for ProjSelfConcordant.ConicExt.hessian_third_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:13:57.961787+00:00
-- url     : https://prove2.me/submissions/479ae468-c5ae-44ec-b250-a252382a6ea1

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

open ProjSelfConcordant.ConicExt
open scoped Topology

theorem solution {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiffOn ℝ 3 f D) (ν : ℝ)
    (q : ℝ × EuclideanSpace ℝ (Fin n)) (hq : q ∈ conicExt D)
    (h : ℝ × EuclideanSpace ℝ (Fin n)) (τ : ℝ) (hτ : 0 < τ) :
    dk 2 (homExt ν f) (τ • q) (τ • h) = dk 2 (homExt ν f) q h ∧
      dk 3 (homExt ν f) (τ • q) (τ • h) = dk 3 (homExt ν f) q h := by
  let S : (ℝ × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      (ℝ × EuclideanSpace ℝ (Fin n)) :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 τ hτ.ne')
  have hS (x : ℝ × EuclideanSpace ℝ (Fin n)) : S x = τ • x := rfl
  have heq : (homExt ν f ∘ S) =ᶠ[𝓝 q]
      (fun x ↦ homExt ν f x - ν * Real.log τ) := by
    have hqpos : 0 < q.1 := hq.1
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hqpos] with x hx
    change homExt ν f (S x) = homExt ν f x - ν * Real.log τ
    rw [hS]
    change ν * (-Real.log (τ * x.1) + f ((τ * x.1)⁻¹ • (τ • x.2))) =
      ν * (-Real.log x.1 + f (x.1⁻¹ • x.2)) - ν * Real.log τ
    have hscale : (τ * x.1)⁻¹ • (τ • x.2) = x.1⁻¹ • x.2 := by
      simp [mul_inv_rev, smul_smul, hτ.ne']
    rw [hscale, Real.log_mul hτ.ne' (ne_of_gt hx)]
    ring
  have hall (k : ℕ) :
      dk (k + 1) (homExt ν f) (τ • q) (τ • h) =
        dk (k + 1) (homExt ν f) q h := by
    have hcomp := S.iteratedFDerivWithin_comp_right (homExt ν f)
      (s := Set.univ) uniqueDiffOn_univ (x := q) (Set.mem_univ _) (k + 1)
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hcomp
    have hconst : iteratedFDeriv ℝ (k + 1)
        (fun x ↦ homExt ν f x - ν * Real.log τ) q =
        iteratedFDeriv ℝ (k + 1) (homExt ν f) q := by
      simp only [iteratedFDeriv_succ_eq_comp_right, fderiv_sub_const]
    have heq' := (heq.iteratedFDeriv ℝ (k + 1)).eq_of_nhds
    rw [hcomp, hconst] at heq'
    have happ := congrArg (fun A ↦ A (fun _ ↦ h)) heq'
    simpa only [dk, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, hS] using happ
  exact ⟨hall 1, hall 2⟩
