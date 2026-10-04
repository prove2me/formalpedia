-- Prove2me | solution 1 for ShorNonsmooth.Subdiff.convex_iff_hessian_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T07:03:52.098499+00:00
-- url     : https://prove2.me/submissions/891d7ddd-0aa2-4b4c-ad0b-f5cb71c26760

import Mathlib

namespace ShorNonsmooth.Subdiff
open Set
noncomputable section

theorem shor_convex_line {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ univ f) (x v : EuclideanSpace ℝ (Fin n)) :
    ConvexOn ℝ univ (fun t : ℝ => f (x+t • v)) := by
  refine ⟨convex_univ,?_⟩
  intro a _ b _ u w hu hw huw
  have h := hf.2 (mem_univ (x+a • v)) (mem_univ (x+b • v)) hu hw huw
  have he : u • (x+a • v)+w • (x+b • v)=x+(u*a+w*b) • v := by
    rw [smul_add,smul_add,smul_smul,smul_smul]
    calc u • x+(u*a) • v+(w • x+(w*b) • v)
        = (u • x+w • x)+((u*a) • v+(w*b) • v) := by abel
      _ = x+(u*a+w*b) • v := by rw [← add_smul,← add_smul,huw,one_smul]
  simpa only [he,smul_eq_mul] using h

theorem shor_line_first {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Differentiable ℝ f) (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x+s • v)) (fderiv ℝ f (x+t • v) v) t := by
  have hl : HasDerivAt (fun s : ℝ => x+s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hf (x+t • v)).hasFDerivAt.comp_hasDerivAt t hl

theorem shor_line_second {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Differentiable ℝ (fderiv ℝ f)) (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (x+s • v) v)
      (fderiv ℝ (fderiv ℝ f) (x+t • v) v v) t := by
  have hl : HasDerivAt (fun s : ℝ => x+s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hc := (hf (x+t • v)).hasFDerivAt.comp_hasDerivAt t hl
  simpa using hc.clm_apply (hasDerivAt_const t v)

theorem shor_hessian_complete {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) :
    ConvexOn ℝ univ f ↔ ∀ x v : EuclideanSpace ℝ (Fin n),
      0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  constructor
  · intro hc x v
    let F : ℝ → ℝ := fun t => f (x+t • v)
    let D : ℝ → ℝ := fun t => fderiv ℝ f (x+t • v) v
    have hD : deriv F=D := by funext t; exact (shor_line_first f hd x v t).deriv
    have hmono : Monotone (deriv F) := by
      intro a b hab
      exact (shor_convex_line f hc x v).monotoneOn_deriv
        (fun t _ => (shor_line_first f hd x v t).differentiableAt)
        (mem_univ a) (mem_univ b) hab
    have hs := (shor_line_second f hd2 x v 0).nonneg_of_monotone (by simpa only [hD] using hmono)
    simpa using hs
  · intro hp
    have hc : ∀ x v : EuclideanSpace ℝ (Fin n),
        ConvexOn ℝ univ (fun t : ℝ => f (x+t • v)) := by
      intro x v
      let F : ℝ → ℝ := fun t => f (x+t • v)
      let D : ℝ → ℝ := fun t => fderiv ℝ f (x+t • v) v
      have hD : deriv F=D := by funext t; exact (shor_line_first f hd x v t).deriv
      apply convexOn_univ_of_deriv2_nonneg
      · intro t
        exact (shor_line_first f hd x v t).differentiableAt
      · rw [hD]
        exact fun t => (shor_line_second f hd2 x v t).differentiableAt
      · intro t
        change 0 ≤ deriv (deriv F) t
        rw [hD,(shor_line_second f hd2 x v t).deriv]
        exact hp _ _
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb hab
    have h := (hc x (y-x)).2 (mem_univ (0:ℝ)) (mem_univ (1:ℝ)) ha hb hab
    have he : x+b • (y-x)=a • x+b • y := by
      rw [smul_sub]
      have he' : a • x+b • x=x := by rw [← add_smul,hab,one_smul]
      calc x+(b • y-b • x) = (a • x+b • x)+(b • y-b • x) := by rw [he']
        _ = a • x+b • y := by abel
    simpa only [smul_eq_mul,mul_zero,mul_one,zero_add,zero_smul,add_zero,one_smul,
      add_sub_cancel,he] using h

end
end ShorNonsmooth.Subdiff

noncomputable section
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) :
    ConvexOn ℝ Set.univ f ↔ ∀ x v : EuclideanSpace ℝ (Fin n),
      0 ≤ fderiv ℝ (fderiv ℝ f) x v v := ShorNonsmooth.Subdiff.shor_hessian_complete f hf
end
#print axioms solution
