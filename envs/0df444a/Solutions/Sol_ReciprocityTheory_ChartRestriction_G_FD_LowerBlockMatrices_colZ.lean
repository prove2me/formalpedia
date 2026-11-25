-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.colZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:36:55.029457+00:00
-- url     : https://prove2.me/submissions/379698e4-f8b9-4a56-bd76-3267d15d17b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BlockIdentityExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowerBlockMatrices
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_col_mul__2f207898769f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_mulVec_eq_sum_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_lowBlock_castLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_lowBlock_kap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mulVec_eq_sum_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_sum_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
theorem _root_.solution (x0 : Frame X.Ψ r) (Z : X.Coord) (τ : X.Ψ) (b : Fin X.p0) :
    col (mat (X.xZ x0 Z) τ) (Fin.castLE X.p0_le b) =
      col (mat x0 τ) (Fin.castLE X.p0_le b) + ∑ a, Z τ a b • col (mat x0 τ) (kap X.p0_le a) := by
  classical
  have hm : mat (X.xZ x0 Z) τ = mat x0 τ * X.lowBlock Z τ := rfl
  have hc : ∀ c k, col (X.lowBlock Z τ) c k = X.lowBlock Z τ k c := fun _ _ ↦ rfl
  rw [hm, col_mul', mulVec_eq_sum_col, sum_split X.p0_le]
  simp only [hc, lowBlock_castLE, lowBlock_kap, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
end ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
