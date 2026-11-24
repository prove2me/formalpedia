-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.perp_kap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:00.369292+00:00
-- url     : https://prove2.me/submissions/299c516b-ac51-4425-85f3-cd584a157292

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_kap_ne_castLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_ortho_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
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
theorem _root_.solution {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (w : Fin r → ℂ) (hw : w ∈ Spos X x τ)
    (a : Fin (r - X.p0)) : hermC τ.1 X.Gm w (col (mat x τ) (kap X.p0_le a)) = 0 := by
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, rfl⟩ := hz
    rw [ortho_apply X hx τ, if_neg (kap_ne_castLE X.p0_le a b).symm]
  | zero => exact hermC_zero_left _ _ _
  | add z1 z2 _ _ h1 h2 => rw [hermC_add_left, h1, h2, add_zero]
  | smul c z _ h => rw [hermC_smul_left, h, mul_zero]
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
