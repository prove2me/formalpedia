-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.rkFam_span_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:30:56.634743+00:00
-- url     : https://prove2.me/submissions/1abc6f2a-e32b-4774-ab7a-099524b5de55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rk_act_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rk_act_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rk_act_zsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rk_act_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
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
variable {dim : (E →+* ℂ) → ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ρ : ℕ} (e : Fin ρ → Vsp dim) (γ : 𝓞 E) (y : Vsp dim)
    (hy : y ∈ Submodule.span ℤ (Set.range (rkFam e))) :
    act γ y ∈ Submodule.span ℤ (Set.range (rkFam e)) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    have hmul : act γ (rkFam e p) = act (γ * RingOfIntegers.basis E p.1) (e p.2) := by
      ext i
      simp [rkFam, rk_act_apply, mul_assoc]
    rw [hmul, ← (RingOfIntegers.basis E).sum_repr (γ * RingOfIntegers.basis E p.1), rk_act_sum]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(l, p.2), rfl⟩)
  | zero =>
    rw [rk_act_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have hxy : act γ (x + y) = act γ x + act γ y := by
      ext i
      simp [rk_act_apply, mul_add]
    rw [hxy]
    exact Submodule.add_mem _ hx hy
  | smul n x _ hx =>
    rw [rk_act_zsmul]
    exact Submodule.smul_mem _ n hx
end ReciprocityTheory.ChartRestriction.G.I2
