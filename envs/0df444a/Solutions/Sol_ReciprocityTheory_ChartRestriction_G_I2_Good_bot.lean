-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Good.bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:55:27.789305+00:00
-- url     : https://prove2.me/submissions/065b6cc4-ca28-4672-aa98-0e6a6580a1dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_zero_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_zero_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_act_eq_actE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
namespace Good
theorem _root_.solution (X : PT E) (c : ℝ) : Good X c ⊥ where
  le := bot_le
  sat := by
    intro x _ hx
    have : IR (⊥ : Submodule ℤ (Vsp X.dim)) = ⊥ := by simp [IR]
    rw [this] at hx
    simpa using hx
  stable := by
    intro α x hx
    rw [Submodule.mem_bot] at hx ⊢
    subst hx
    rw [act_eq_actE, actE_zero_right]
  iso := by
    intro x hx y _
    rw [Submodule.mem_bot] at hx
    subst hx
    exact Hf_im_zero_left y
  sep := by
    intro x _ u hu hne
    exfalso
    have : IR (⊥ : Submodule ℤ (Vsp X.dim)) = ⊥ := by simp [IR]
    have h1 := hu.1
    rw [this, Submodule.mem_bot] at h1
    exact hne h1
end Good
end ReciprocityTheory.ChartRestriction.G.I2
