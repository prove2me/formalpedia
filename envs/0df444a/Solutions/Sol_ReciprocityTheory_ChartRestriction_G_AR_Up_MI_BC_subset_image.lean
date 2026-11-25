-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.BC_subset_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:18.139009+00:00
-- url     : https://prove2.me/submissions/d950a613-749e-4858-8588-7f1f5fe4e2ae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_Lemmata_GeneralBFactForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lu_exists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution : BC ι r ⊆ lu '' sS ι r := by
  intro v hv
  choose N U hN hN1 hU hUd hNU using fun τ => lu_exists (M := Mt v τ) (hv τ)
  refine ⟨fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2 else U i.1 i.2.1 i.2.2, ?_, ?_⟩
  · intro τ b
    show (if b < b then N τ b b else U τ b b) ≠ 0
    rw [if_neg (lt_irrefl b)]
    intro h0
    have hdet : (U τ).det = ∏ b, U τ b b := Matrix.det_of_upperTriangular (hU τ)
    exact hUd τ (hdet ▸ Finset.prod_eq_zero (Finset.mem_univ b) h0)
  · have hsl : ∀ τ, 1 + sl (fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2
        else U i.1 i.2.1 i.2.2) τ = N τ := by
      intro τ
      ext a b
      rcases lt_trichotomy b a with h | h | h
      · simp [sl, h, Matrix.one_apply_ne (ne_of_gt h)]
      · subst h
        simp [sl, hN1]
      · have h0 : N τ a b = 0 := hN τ (OrderDual.toDual_lt_toDual.mpr h)
        simp [sl, not_lt.mpr h.le, Matrix.one_apply_ne (ne_of_lt h), h0]
    have hup : ∀ τ, up (fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2
        else U i.1 i.2.1 i.2.2) τ = U τ := by
      intro τ
      ext a b
      by_cases h : b < a
      · have h0 : U τ a b = 0 := hU τ h
        simp [up, h, h0]
      · simp [up, h]
    funext i
    obtain ⟨τ, a, b⟩ := i
    show ((1 + sl _ τ) * up _ τ : Matrix (Fin r) (Fin r) ℂ) a b = v (τ, a, b)
    rw [hsl, hup, hNU]
    rfl
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
