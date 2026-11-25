-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ct_itD_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:23:29.358924+00:00
-- url     : https://prove2.me/submissions/efdd8cf9-1e97-43ad-9524-38aee1720e9b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_itD_contDiff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_itD_cons_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_itD_cons


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) {l₁ l₂ : List W} (h : l₁.Perm l₂) :
    (fun y => itD f l₁ y) = fun y => itD f l₂ y := by
  induction h with
  | nil => rfl
  | @cons x l₁ l₂ _ ih =>
    funext y
    rw [itD_cons hf, itD_cons hf, ih]
  | @swap x y l =>
    funext z
    rw [ct_itD_cons_cons hf, ct_itD_cons_cons hf]
    have hg := ct_itD_contDiff hf l
    have hs : IsSymmSndFDerivAt ℂ (fun y => itD f l y) z := by
      refine hg.contDiffAt.isSymmSndFDerivAt ?_
      try simp only [minSmoothness_of_isRCLikeNormedField]
      first
        | exact WithTop.coe_le_coe.2 le_top
        | exact (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
        | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
        | norm_num
        | decide
    exact hs y x
  | @trans l₁ l₂ l₃ _ _ ih1 ih2 => rw [ih1, ih2]
end ReciprocityTheory.ChartRestriction.G.I2
