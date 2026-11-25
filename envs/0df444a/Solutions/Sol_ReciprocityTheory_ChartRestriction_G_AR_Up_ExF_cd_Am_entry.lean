-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.cd_Am_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:47:23.361826+00:00
-- url     : https://prove2.me/submissions/948e26d2-aa6a-42d0-98aa-95d8560dc809

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_cd_Zt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution (τ : X.Ψ) (a c : Fin X.p0) :
    ContDiff ℝ ∞ fun z : V (nd X) => Am X z τ a c := by
  have hZ : ∀ a m, ContDiff ℝ ∞ fun z : V (nd X) => Zt X z τ a m :=
    fun a m => (cd_Zt X τ a m).restrict_scalars ℝ
  have hfun : (fun z : V (nd X) => Am X z τ a c) = fun z =>
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a c - ∑ m, Zt X z τ a m * star (Zt X z τ c m) := by
    funext z
    simp only [Am, Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hfun]
  refine contDiff_const.sub (ContDiff.sum fun m _ => (hZ a m).mul ?_)
  first
    | exact (hZ c m).star
    | exact Complex.conjCLE.contDiff.comp (hZ c m)
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
