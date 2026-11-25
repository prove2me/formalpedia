-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IW.gram_cpt_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:13.744275+00:00
-- url     : https://prove2.me/submissions/69ff5161-a026-4114-8a27-055abfc27e1a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_cpt_entry_cd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW
theorem _root_.solution (x0 : Frame X.Ψ r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℝ ∞ fun z : V (nd X) => FD.gram τ.1 X.Gm (mat (cpt X x0 z) τ) a b := by
  have hc : ∀ a b : Fin r, ContDiff ℝ ∞ fun z : V (nd X) => cpt X x0 z τ a b :=
    fun a b => (cpt_entry_cd X x0 τ a b).restrict_scalars ℝ
  have hcj : ∀ a b : Fin r, ContDiff ℝ ∞ fun z : V (nd X) => (starRingEnd ℂ) (cpt X x0 z τ a b) := by
    intro a b
    first
    | exact Complex.conjCLE.contDiff.comp (hc a b)
    | simpa [Function.comp_def] using Complex.conjCLE.contDiff.comp (hc a b)
  simp only [gram, hermC, col, Matrix.of_apply, mat]
  refine ContDiff.sum (fun k _ => ContDiff.sum (fun l _ => ?_))
  exact ((hc k a).mul contDiff_const).mul (hcj l b)
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
