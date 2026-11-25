-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.rkQP_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:12:53.003383+00:00
-- url     : https://prove2.me/submissions/842bfbaa-9927-44b3-9c0a-15f6f5c96cb0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitR
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
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (τ : E →+* ℂ) (v : Vsp dim) (i : Idx dim) :
    rkQ τ (rkP τ v) i = if i.1 = τ then v i else 0 := by
  obtain ⟨σ, b⟩ := i
  by_cases h : σ = τ
  · subst h
    simp [rkQ, rkP, EuclideanSpace.single_apply, Sigma.mk.inj_iff]
    rw [Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      rw [Pi.single_apply, if_neg]
      · simp
      · intro h
        apply hx
        exact (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · intro h
      exact absurd (Finset.mem_univ b) h
  · simp [rkQ, rkP, EuclideanSpace.single_apply, Sigma.mk.inj_iff, h]
end ReciprocityTheory.ChartRestriction.G.I2
