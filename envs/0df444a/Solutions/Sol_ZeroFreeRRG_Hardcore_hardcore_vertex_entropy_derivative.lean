-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_vertex_entropy_derivative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:48:42.388203+00:00
-- url     : https://prove2.me/submissions/9eb911ee-0645-4407-b1d4-17dd411cd18d

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_vertex_factor_derivative
import Mathlib
set_option autoImplicit false
open scoped BigOperators
open ZeroFreeRRG.Hardcore

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → ℝ) (θ : ℝ)
    (hden : 1+θ ≠ 0)
    (hV : ((∏ i, (1+θ*h i)) + θ*(∏ i, (1-h i)))/(1+θ) ≠ 0) :
    HasDerivAt
      (fun t : ℝ => let V := ((∏ i, (1+t*h i)) + t*(∏ i, (1-h i)))/(1+t)
        V * Real.log V)
      ((((1+θ)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+θ*h j))*h i) +
          (∏ i, (1-h i)) - ∏ i, (1+θ*h i)) / (1+θ)^2) *
        (Real.log (((∏ i, (1+θ*h i)) + θ*(∏ i, (1-h i)))/(1+θ)) + 1)) θ := by
  let V := fun t : ℝ => ((∏ i, (1+t*h i)) + t*(∏ i, (1-h i)))/(1+t)
  let D := ((1+θ)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+θ*h j))*h i) +
          (∏ i, (1-h i)) - ∏ i, (1+θ*h i)) / (1+θ)^2
  have hv : HasDerivAt V D θ := hardcore_vertex_factor_derivative h θ hden
  have hl := hv.log hV
  have hm := hv.mul hl
  change HasDerivAt (fun t => V t * Real.log (V t)) (D * (Real.log (V θ)+1)) θ
  have hv0 : V θ ≠ 0 := hV
  have heq : D * (Real.log (V θ)+1) = D * Real.log (V θ) + V θ * (D / V θ) := by
    field_simp
  rw [heq]
  exact hm
