-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.quad_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:06.718919+00:00
-- url     : https://prove2.me/submissions/1e90303e-c10b-4d4f-bc01-25626e7395d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_ipB_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_ip_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
open Matrix NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
theorem _root_.solution (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (g : Basis ι ℤ X.Λ) (x : ι → ℝ) :
    x ⬝ᵥ (Am X y g *ᵥ x) = ip X (Ly X y (∑ i, x i • X.embV (g i : Fin r → E)))
      (Ly X y (∑ i, x i • X.embV (g i : Fin r → E))) := by
  have hL : Ly X y (∑ i, x i • X.embV (g i : Fin r → E)) =
      ∑ i, x i • Ly X y (X.embV (g i : Fin r → E)) := by
    simp only [map_sum, map_smul]
  rw [hL, ← ipB_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ipB_apply]
  simp only [dotProduct, Matrix.mulVec, Am, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ip_comm X (Ly X y (X.embV (g j : Fin r → E)))]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
