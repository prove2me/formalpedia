-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUB.cell_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:32:22.104896+00:00
-- url     : https://prove2.me/submissions/79625244-342d-4f62-8ee4-fd2073fae2f7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_nmat_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_orth_mem_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoS_dom_rmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
theorem _root_.solution (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) :
    cpt X (rmul x1' b1) 0 ∈ ExtFPf.cell D := by
  have h0 : cpt X (rmul x1' b1) 0 = rmul x1' b1 := by
    funext τ
    show (mat (rmul x1' b1) τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = rmul x1' b1 τ
    rw [IW.nmat_zero, Matrix.mul_one]
    rfl
  have hx0 : cpt X x1' 0 = x1' := by
    funext τ
    show (mat x1' τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x1' τ
    rw [IW.nmat_zero, Matrix.mul_one]
    rfl
  have hdom : x1' ∈ X.dom := IW.orth_mem_dom X x1' ho'
  have hO : (0 : V (nd X)) ∈ OmF X x1' := by
    show cpt X x1' 0 ∈ X.dom
    rw [hx0]
    exact hdom
  have hu := (D.uniq 0 hO b1 hb1).1
  rw [hx0] at hu
  rw [h0]
  exact ⟨OntoS.dom_rmul X hdom hb1, hu⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
