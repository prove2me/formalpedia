-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.zero_of_mem_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:31.57549+00:00
-- url     : https://prove2.me/submissions/60cef148-57dc-4df0-bb7e-0a3d4206cd73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_eq_zero_of_Pos_Neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_perp_kap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_re_self_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
theorem _root_.solution {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0)
    (w : Fin r → ℂ) (hw : w ∈ Spos X x τ) (h0 : hermC τ.1 X.Gm w w = 0) : w = 0 := by
  have hre := re_self_of_mem X hx τ hdet w hw
  rw [h0, Complex.zero_re] at hre
  have hN : Neg X x τ w = 0 := by
    unfold Neg
    exact Finset.sum_eq_zero (fun a _ => by rw [perp_kap X hx τ w hw a]; simp)
  exact eq_zero_of_Pos_Neg X hx τ hdet w hre.symm hN
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
