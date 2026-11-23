-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.cf_mapC_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:39.728467+00:00
-- url     : https://prove2.me/submissions/79684eff-82ca-4185-b275-703338e33a52

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Filter Topology Polynomial Matrix
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution {α β γ : Type*} [Fintype β] (n : ℕ) (A : Matrix α β ℂ)
    (P : Matrix β γ ℂ[X]) : cf n (A.map C * P) = A * cf n P := by
  ext i j
  simp only [cf, Matrix.map_apply, Matrix.mul_apply, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]
end ReciprocityTheory.AnForm.P
