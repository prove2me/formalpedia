-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.isOpen_OmF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:27:21.235975+00:00
-- url     : https://prove2.me/submissions/c93e1886-a453-49a4-8563-50d40c23c68f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_cd_nM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mat_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mem_dom_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


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
theorem _root_.solution (x0 : Frame X.Ψ r) : IsOpen (OmF X x0) := by
  have hc : Continuous fun z : V (nd X) => cpt X x0 z := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    have hfun : (fun z : V (nd X) => cpt X x0 z τ a b) = fun z => ∑ k, x0 τ a k * nM X z τ k b := by
      funext z
      have h := congrFun (congrFun (mat_cpt X x0 z τ) a) b
      simpa [mat, Matrix.mul_apply] using h
    rw [hfun]
    exact continuous_finset_sum _ fun k _ => continuous_const.mul (cd_nM X τ k b).continuous
  have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := fun τ =>
    continuous_pi fun a => continuous_pi fun b =>
      (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det :=
    fun τ => (hmat τ).matrix_det
  have hdmin : ∀ τ i, Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    refine Continuous.matrix_det ?_
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.submatrix_apply, FD.gram, Matrix.of_apply, FD.hermC, FD.col, mat]
    fun_prop
  have hset : OmF X x0 = ⋂ τ : X.Ψ, ({z | (mat (cpt X x0 z) τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {z | 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re}) := by
    ext z
    simp only [OmF, Set.mem_setOf_eq, X.mem_dom_iff, Set.mem_iInter, Set.mem_inter_iff]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun ((hdet τ).comp hc) continuous_const
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp ((hdmin τ i).comp hc)))
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
