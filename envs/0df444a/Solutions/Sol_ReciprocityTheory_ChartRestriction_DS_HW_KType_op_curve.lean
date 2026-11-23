-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.KType.op_curve
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:06:36.547922+00:00
-- url     : https://prove2.me/submissions/8b7bd1fb-e866-4575-a6e1-9d7f45678c06

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_onep_KG_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
namespace KType
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    T.op (γ t) = NormedSpace.exp ((t : ℂ) • T.dτ X) := by
  set A := T.dτ X with hAdef
  set F : ℝ → T.V →L[ℂ] T.V := fun s => T.op (γ s) with hFdef
  have hmul : ∀ s u : ℝ, γ (s + u) = γ s * γ u := by
    intro s u
    apply onep_KG_ext
    show toMK (γ (s + u)) = toMK (γ s) * toMK (γ u)
    rw [hγ, hγ, hγ, show (((s + u : ℝ) : ℂ) • X) = (s : ℂ) • X + (u : ℂ) • X by push_cast; exact add_smul _ _ _]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)
  have h0 : γ 0 = 1 := by
    apply onep_KG_ext
    rw [hγ]
    show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = (1 : Matrix (Fin n) (Fin n) ℂ)
    simp
  have hF : ∀ s u : ℝ, F (s + u) = F s * F u := by
    intro s u
    simp only [hFdef, KType.op, hmul, map_mul]
    rfl
  have hF0 : F 0 = 1 := by
    simp only [hFdef, KType.op, h0, map_one]
    rfl
  have hd0 : HasDerivAt F A 0 := T.hasDeriv X hX γ hγ
  have hd : ∀ s, HasDerivAt F (F s * A) s := by
    intro s
    have h1 : HasDerivAt (fun u => F s * F (u - s)) (F s * A) s := by
      have h2 := hd0.const_mul (F s)
      rw [← sub_self s] at h2
      exact HasDerivAt.comp_sub_const (f := fun y => F s * F y) s s h2
    convert h1 using 1
    funext u
    rw [← hF, add_sub_cancel]
  set E : ℝ → T.V →L[ℂ] T.V := fun u => NormedSpace.exp (u • (-A)) with hEdef
  have hE : ∀ u, HasDerivAt E (E u * (-A)) u := fun u => hasDerivAt_exp_smul_const (-A) u
  have hcomm : ∀ u, A * E u = E u * A := fun u =>
    (((Commute.refl A).neg_right.smul_right u).exp_right).eq
  have hG : ∀ u, HasDerivAt (F * E) 0 u := by
    intro u
    refine ((hd u).mul (hE u)).congr_deriv ?_
    simp only [mul_neg, mul_assoc, hcomm u, add_neg_cancel]
  have hGc : ∀ u, (F * E) u = (F * E) 0 := fun u =>
    is_const_of_deriv_eq_zero (fun v => (hG v).differentiableAt) (fun v => (hG v).deriv) u 0
  have hG0 : (F * E) 0 = 1 := by
    show F 0 * NormedSpace.exp ((0 : ℝ) • (-A)) = 1
    rw [hF0, zero_smul, NormedSpace.exp_zero, one_mul]
  show F t = _
  have hs : ((t : ℂ) • A) = t • A := by
    exact Complex.coe_smul t A
  rw [hs]
  have hc : Commute (t • (-A)) (t • A) := (((Commute.refl A).neg_left).smul_left t).smul_right t
  calc F t = F t * E t * NormedSpace.exp (t • A) := by
        rw [mul_assoc, hEdef, ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc
          ((NormedSpace.expSeries_radius_eq_top ℝ (T.V →L[ℂ] T.V)).symm ▸ edist_lt_top _ _)
          ((NormedSpace.expSeries_radius_eq_top ℝ (T.V →L[ℂ] T.V)).symm ▸ edist_lt_top _ _), smul_neg, neg_add_cancel,
          NormedSpace.exp_zero, mul_one]
    _ = NormedSpace.exp (t • A) := by
        rw [show F t * E t = (F * E) t from rfl, hGc, hG0, one_mul]
end KType
end ReciprocityTheory.ChartRestriction.DS.HW
