-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.gaussianInner_monomial_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:27:55.032153+00:00
-- url     : https://prove2.me/submissions/f7c5f954-b247-4868-a289-86a210831ef2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paMono_rot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (q : ℕ) {α β : ι →₀ ℕ} (h : α ≠ β) : paIP q (paMono α) (paMono β) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ β j := by
    by_contra hc
    push_neg at hc
    exact h (Finsupp.ext hc)
  have hab : ((α j : ℝ) - β j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hj)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, ((α j : ℝ) - β j) * θ = Real.pi :=
    ⟨Real.pi / ((α j : ℝ) - β j), by field_simp⟩
  have hc : ((α j : ℂ) - β j) * θ = Real.pi := by exact_mod_cast hθ
  have hfac : ((Circle.exp θ : Circle) : ℂ) ^ (α j) *
      (starRingEnd ℂ) (((Circle.exp θ : Circle) : ℂ) ^ (β j)) = -1 := by
    rw [Circle.coe_exp, map_pow, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_add, ← Complex.exp_pi_mul_I]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    linear_combination I * hc
  have hw : ∀ v, paW q (jRot j (Circle.exp θ) v) = paW q v := by
    intro v
    simp only [paW, LinearIsometryEquiv.norm_map]
  have key : ∀ v, paMono α (jRot j (Circle.exp θ) v) * (starRingEnd ℂ) (paMono β (jRot j (Circle.exp θ) v)) *
      (paW q (jRot j (Circle.exp θ) v) : ℂ) = -(paMono α v * (starRingEnd ℂ) (paMono β v) * (paW q v : ℂ)) := by
    intro v
    rw [paMono_rot, paMono_rot, hw, map_mul]
    linear_combination (paMono α v * (starRingEnd ℂ) (paMono β v) * (paW q v : ℂ)) * hfac
  have hI : paIP q (paMono α) (paMono β) = -paIP q (paMono α) (paMono β) := by
    unfold paIP
    rw [← integral_neg]
    conv_lhs =>
      rw [← ((jRot j (Circle.exp θ)).measurePreserving).integral_comp
        (jRot j (Circle.exp θ)).toHomeomorph.measurableEmbedding]
    congr 1
    funext v
    exact key v
  linear_combination hI / 2
end ReciprocityTheory.ChartRestriction.G.I2.FPw
