-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.cf_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:53.450662+00:00
-- url     : https://prove2.me/submissions/c6f80e00-c441-4070-a7df-8fe2c05ae0f1

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
theorem _root_.solution {α β γ : Type*} [Fintype β] (n : ℕ) (P : Matrix α β ℂ[X]) (Q : Matrix β γ ℂ[X]) :
    cf n (P * Q) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, cf x.1 P * cf x.2 Q := by
  ext i j
  simp only [cf, Matrix.map_apply, Matrix.mul_apply, Polynomial.finset_sum_coeff, Polynomial.coeff_mul,
    Matrix.sum_apply]
  exact Finset.sum_comm
end ReciprocityTheory.AnForm.P
