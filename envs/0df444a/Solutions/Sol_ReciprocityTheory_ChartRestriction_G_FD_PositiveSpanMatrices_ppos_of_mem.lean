-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.ppos_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:55.033468+00:00
-- url     : https://prove2.me/submissions/825507ac-6ed1-4c4d-bd6c-09f9c6e194fc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left


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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ) (hw : w ∈ Spos X x τ) :
    X.ppos x τ w = w := by
  obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
  have hu : IsUnit (X.gramPos x τ).det := by
    open scoped ComplexOrder in
    exact (Matrix.isUnit_iff_isUnit_det _).mp (X.gramPos_posDef hx τ).isUnit
  have hin : ∀ b, hermC τ.1 X.Gm (∑ a, t a • col (mat x τ) (Fin.castLE X.p0_le a))
      (col (mat x τ) (Fin.castLE X.p0_le b)) = ∑ a, t a * X.gramPos x τ a b := by
    intro b
    rw [hermC_sum_left]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hermC_smul_left, X.gramPos_apply]
    rfl
  unfold Data.ppos
  simp_rw [hin]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  have e : ∑ b, (∑ a', t a' * X.gramPos x τ a' b) * (X.gramPos x τ)⁻¹ b a =
      Matrix.vecMul (Matrix.vecMul t (X.gramPos x τ)) (X.gramPos x τ)⁻¹ a := rfl
  rw [e, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
