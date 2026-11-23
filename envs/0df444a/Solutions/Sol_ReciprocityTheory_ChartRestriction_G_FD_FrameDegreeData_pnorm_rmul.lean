-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:44.982353+00:00
-- url     : https://prove2.me/submissions/55f03f0b-62ad-4c18-88c3-495d9caf1470

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bdiag_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_ratio_rmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_factor_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) : X.pnorm la P (rmul x b) = X.pnorm la P x := by
  have hfac : ∀ (τ : X.Ψ) (i : Fin r), ‖b τ i i‖ ^ la τ i *
      (‖b τ i i‖ ^ 2 * ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖) ^ (-(la τ i : ℝ) / 2) =
      ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) :=
    fun τ i => factor_eq _ _ (norm_pos_iff.2 (bdiag_ne X hb τ i)) (norm_nonneg _) _
  unfold Data.pnorm
  rw [hP x hx b hb, norm_mul]
  simp only [ratio_rmul X x hx hb]
  unfold bchar
  simp only [norm_prod, norm_zpow]
  rw [← Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => hfac τ i]
  simp only [Finset.prod_mul_distrib]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
