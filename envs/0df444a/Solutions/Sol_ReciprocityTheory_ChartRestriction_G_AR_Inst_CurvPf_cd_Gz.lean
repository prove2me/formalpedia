-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cd_Gz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:51.941373+00:00
-- url     : https://prove2.me/submissions/6aa664b9-0b41-471f-8a0c-4fcfded69225

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_conjT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_lin

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
open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (a b : Fin m) : ContDiff ℝ 2 fun v : Fin 1 → ℂ => Gz hm D Y (v 0) a b := by
  have hl : ∀ i j : Fin r, ContDiff ℝ 2 fun v : Fin 1 → ℂ => (1 + v 0 • Y) i j := by
    intro i j
    have h := cd_lin Y 1 i j
    simp only [one_mul] at h
    exact h
  show ContDiff ℝ 2 fun v : Fin 1 → ℂ =>
    ((1 + v 0 • Y)ᴴ * Dc D * (1 + v 0 • Y) : Matrix (Fin r) (Fin r) ℂ) (Fin.castLE hm a) (Fin.castLE hm b)
  exact cd_mul (fun v : Fin 1 → ℂ => (1 + v 0 • Y)ᴴ * Dc D) (fun v => 1 + v 0 • Y)
    (fun i j => cd_mul (fun v : Fin 1 → ℂ => (1 + v 0 • Y)ᴴ) (fun _ => Dc D)
      (cd_conjT (fun v : Fin 1 → ℂ => 1 + v 0 • Y) hl) (fun _ _ => contDiff_const) i j) hl _ _
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
