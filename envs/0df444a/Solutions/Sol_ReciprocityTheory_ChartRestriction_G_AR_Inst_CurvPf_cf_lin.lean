-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cf_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:47.352291+00:00
-- url     : https://prove2.me/submissions/c7c4c606-c744-45dc-a4df-f4b386f3ed31

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Polynomial Matrix ReciprocityTheory.AnForm.P
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    cf k (lin A) = if k = 0 then 1 else if k = 1 then A else 0 := by
  ext i j
  rcases k with _ | _ | k <;> by_cases h : i = j <;>
    simp [cf, lin, Matrix.one_apply, h, Polynomial.coeff_one, Polynomial.coeff_C]
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
