-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.levi_logNormSq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:17.906457+00:00
-- url     : https://prove2.me/submissions/1af5b2f8-f596-46e0-8964-dd7c154d545d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhE_two_le_infty
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviLogNormSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution {n : ℕ} (h : V n → ℂ) (hh : ContDiff ℂ ∞ h) (v0 : V n)
    (hne : h v0 ≠ 0) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Real.log (Complex.normSq (h y)) : ℝ) : ℂ)) v0 ξ = 0 := by
  have hl := ReciprocityTheory.L2DbarEstimates.H.leviLogNormSq n 1 (fun _ => h) v0 ξ
    (fun _ => hh.contDiffAt.of_le two_le_infty) (by intro h'; exact hne (congrFun h' 0))
  have e1 : (fun y => ((Real.log (sqNorm (fun i : Fin 1 => (fun _ => h) i y)) : ℝ) : ℂ)) =
      fun y => ((Real.log (Complex.normSq (h y)) : ℝ) : ℂ) := by
    funext y; simp [sqNorm]
  rw [e1] at hl
  rw [hl]
  have hn : (Complex.normSq (h v0) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.2 hne).ne'
  have hP : projPerp (fun _ : Fin 1 => h v0) = 0 := by
    ext i l
    fin_cases i; fin_cases l
    simp [projPerp, sqNorm, vecMulVec_apply, Complex.mul_conj, hn]
  simp [hP, sqNorm]
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
