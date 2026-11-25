-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.perp_of_ppos_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:36:09.363849+00:00
-- url     : https://prove2.me/submissions/681c1211-a6ed-48dc-a149-0d96dbb8e3be

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_zero_left


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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ)
    (hw : X.ppos x τ w = 0) (b : Fin X.p0) : hermC τ.1 X.Gm w (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
  have hu : IsUnit (X.gramPos x τ).det := by
    open scoped ComplexOrder in
    exact (Matrix.isUnit_iff_isUnit_det _).mp (X.gramPos_posDef hx τ).isUnit
  have h1 : hermC τ.1 X.Gm (X.ppos x τ w) (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
    rw [hw, hermC_zero_left]
  unfold Data.ppos at h1
  rw [hermC_sum_left] at h1
  simp_rw [hermC_smul_left] at h1
  have e2 : ∀ a, hermC τ.1 X.Gm (col (mat x τ) (Fin.castLE X.p0_le a)) (col (mat x τ) (Fin.castLE X.p0_le b)) =
      X.gramPos x τ a b := fun a => (X.gramPos_apply x τ a b).symm
  simp_rw [e2] at h1
  have e : ∑ a, (∑ b', hermC τ.1 X.Gm w (col (mat x τ) (Fin.castLE X.p0_le b')) * (X.gramPos x τ)⁻¹ b' a) *
      X.gramPos x τ a b =
      Matrix.vecMul (Matrix.vecMul (fun b' => hermC τ.1 X.Gm w (col (mat x τ) (Fin.castLE X.p0_le b')))
        (X.gramPos x τ)⁻¹) (X.gramPos x τ) b := rfl
  rw [e, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one] at h1
  exact h1
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
