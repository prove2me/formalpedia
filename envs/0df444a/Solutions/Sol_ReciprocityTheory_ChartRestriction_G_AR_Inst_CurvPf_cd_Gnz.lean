-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cd_Gnz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:05.626446+00:00
-- url     : https://prove2.me/submissions/f342626c-0108-4cd9-9799-8f3cad89a646

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_conjT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_lin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_cd_Gz

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
theorem _root_.solution (a b : Fin m) : ContDiff ℝ 2 fun v : Fin 1 → ℂ => Gnz hm D Y (v 0) a b := by
  have hl : ∀ i j : Fin m, ContDiff ℝ 2 fun v : Fin 1 → ℂ => (1 - v 0 • Ym hm Y) i j := by
    intro i j
    have h := cd_lin (Ym hm Y) (-1) i j
    have e : ∀ v : Fin 1 → ℂ, (1 + (-1 * v 0) • Ym hm Y) = 1 - v 0 • Ym hm Y := by
      intro v
      rw [neg_one_mul, neg_smul, ← sub_eq_add_neg]
    simp only [e] at h
    exact h
  show ContDiff ℝ 2 fun v : Fin 1 → ℂ =>
    ((1 - v 0 • Ym hm Y)ᴴ * (Gz hm D Y (v 0) * (1 - v 0 • Ym hm Y)) : Matrix (Fin m) (Fin m) ℂ) a b
  exact cd_mul (fun v : Fin 1 → ℂ => (1 - v 0 • Ym hm Y)ᴴ)
    (fun v => Gz hm D Y (v 0) * (1 - v 0 • Ym hm Y))
    (cd_conjT (fun v : Fin 1 → ℂ => 1 - v 0 • Ym hm Y) hl)
    (fun i j => cd_mul (fun v : Fin 1 → ℂ => Gz hm D Y (v 0)) (fun v => 1 - v 0 • Ym hm Y)
      (fun i j => cd_Gz hm D Y i j) hl i j) a b
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
