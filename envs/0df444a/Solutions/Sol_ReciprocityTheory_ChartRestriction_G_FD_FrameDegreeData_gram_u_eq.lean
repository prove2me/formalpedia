-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_u_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:35:12.364964+00:00
-- url     : https://prove2.me/submissions/2744fb33-0e8c-4180-8ede-6d0dea676a58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_uGu_lower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_blk_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_gram_isHermitian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat x τ * uOf X x τ) = Matrix.diagonal (dOf X x τ) := by
  ext c a
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rfl
  · rcases lt_or_gt_of_ne h with h' | h'
    · have hH := gram_isHermitian τ.1 X.Gm_herm (mat x τ * uOf X x τ)
      rw [← hH.apply c a, uOf, gram_mul, uGu_lower _ (blk_det X hx τ) h', star_zero]
    · rw [uOf, gram_mul, uGu_lower _ (blk_det X hx τ) h']
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
