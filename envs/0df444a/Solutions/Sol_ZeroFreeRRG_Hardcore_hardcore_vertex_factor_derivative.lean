-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_vertex_factor_derivative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:38:25.091625+00:00
-- url     : https://prove2.me/submissions/5c8826da-7b8e-4525-95da-9f578916e651

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → ℝ) (θ : ℝ)
    (hden : 1+θ ≠ 0) :
    HasDerivAt (fun t : ℝ => ((∏ i, (1+t*h i)) + t*(∏ i, (1-h i)))/(1+t))
      (((1+θ)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+θ*h j))*h i) +
          (∏ i, (1-h i)) - ∏ i, (1+θ*h i)) / (1+θ)^2) θ := by
  have hP : HasDerivAt (fun t : ℝ => ∏ i, (1+t*h i))
      (∑ i, (∏ j ∈ Finset.univ.erase i, (1+θ*h j))*h i) θ := by
    have hh := HasDerivAt.fun_finsetProd (x := θ) (u := Finset.univ)
      (f := fun (i : ι) (t : ℝ) => 1+t*h i) (f' := fun i => h i)
      (fun i hi => by simpa only [one_mul,id_eq] using ((hasDerivAt_id θ).mul_const (h i)).const_add 1)
    simpa only [smul_eq_mul] using hh
  have hB : HasDerivAt (fun t : ℝ => t*(∏ i, (1-h i))) (∏ i, (1-h i)) θ := by
    simpa using (hasDerivAt_id θ).mul_const (∏ i, (1-h i))
  have hN := hP.fun_add hB
  have hD : HasDerivAt (fun t : ℝ => 1+t) 1 θ := by
    exact (hasDerivAt_id θ).const_add 1
  have hh := hN.fun_div hD hden
  have heq : ((∑ i, (∏ j ∈ Finset.univ.erase i, (1+θ*h j))*h i) + ∏ i, (1-h i))*(1+θ) -
      ((∏ i, (1+θ*h i)) + θ*(∏ i, (1-h i))) * 1 =
      (1+θ)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+θ*h j))*h i) +
        (∏ i, (1-h i)) - ∏ i, (1+θ*h i) := by ring
  simpa only [heq] using hh
