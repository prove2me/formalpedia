-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.four_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:51:36.123822+00:00
-- url     : https://prove2.me/submissions/b80f28fd-c055-4f61-b65e-8804c267332a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_descend
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_torus_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_shift_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_shift_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_iper_of_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_continuous_rl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_Av_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_mF_ex
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_Pm_diff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_Pm_per

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimB
variable {k : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_11
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_13
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_16
namespace ReciprocityTheory.ChartRestriction.G.I2.DimB
theorem _root_.solution {q : ℕ} (hq : 0 < q) (h : (Fin k → ℂ) → ℂ) (hd : Differentiable ℂ h)
    (hp1 : ∀ l z, h (z + Pi.single l 1) = h z) (τ : Fin k → Fin k → ℂ) (C : Fin k → ℂ)
    (hqp : ∀ j z, h (z + τ j) = C j * cexp (2 * Real.pi * I * q * z j) * h z)
    (hc : ∀ m : Fin k → ℤ, (∀ l, 0 ≤ m l ∧ m l < q) → Av (Pm h m) 0 = 0) : h = 0 := by
  have hp := iper_of_unit h hp1
  by_cases hC : ∃ j, C j = 0
  · obtain ⟨j, hj⟩ := hC
    funext z
    have := hqp j (z - τ j)
    rw [sub_add_cancel, hj] at this; simpa using this
  push Not at hC
  have hrec : ∀ j m, Av (Pm h m) 0 =
      C j * ex m (τ j) * Av (Pm h (m - (q : ℤ) • Pi.single j 1)) 0 := by
    intro j m
    rw [← Av_const _ (Pm_diff h hd m) (Pm_per h hp m) (τ j)]
    unfold Av
    rw [← integral_const_mul]
    congr 1; funext x
    simp only [Pm, add_zero, ex_add, hqp j, ← ex_shift]; ring
  let P : (Fin k → ℤ) → Prop := fun m => Av (Pm h m) 0 = 0
  have Z : ∀ j m, P (m + (q : ℤ) • (Pi.single j 1 : Fin k → ℤ)) = P m := by
    intro j m
    show (Av (Pm h (m + (q : ℤ) • (Pi.single j 1 : Fin k → ℤ))) 0 = 0) = (Av (Pm h m) 0 = 0)
    rw [hrec j (m + _), add_sub_cancel_right]
    apply propext
    simp [hC j, ex_ne]
  have hall : ∀ m, Av (Pm h m) 0 = 0 := by
    intro m
    have hm : m = (fun l => m l % q) + ∑ l, (m l / q) • ((q : ℤ) • Pi.single l (1 : ℤ)) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
      linear_combination -(Int.emod_add_mul_ediv (m i) q)
    have := shift_sum (G := Fin k → ℤ) (β := Prop) P
      (fun l => (m l / q) • ((q : ℤ) • (Pi.single l 1 : Fin k → ℤ)))
      (fun l v => shift_int (G := Fin k → ℤ) (β := Prop) P _ (Z l) _ v) Finset.univ (fun l => m l % q)
    rw [← hm] at this
    show P m
    rw [this]
    exact hc _ (fun l => ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩)
  have hz : ∀ x y : Fin k → ℝ, h (rl x + fun i => I * (y i : ℂ)) = 0 := by
    intro x y
    set w : Fin k → ℂ := fun i => I * (y i : ℂ)
    obtain ⟨D, hD⟩ := descend (fun x => h (rl x + w))
      (hd.continuous.comp (continuous_rl.add continuous_const)) (fun n t => by
        have e : rl (t + fun i => (n i : ℝ)) + w = (rl t + w) + iz n := by
          funext i; simp [rl, iz]; ring
        simp only [e, hp n])
    have hD0 : D = 0 := torus_unique D (fun m => by
      rw [UnitAddTorus.mFourierCoeff_eq_integral _ m 0]
      have e : ∀ x : Fin k → ℝ, UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle)) •
          D (fun i => (x i : UnitAddCircle)) = (ex m w)⁻¹ * Pm h m (rl x + w) := by
        intro x
        have h1 := mF_ex m x
        have h2 := hD x
        rw [show (fun i => (x i : UnitAddCircle)) = tproj x from rfl, h1, h2, smul_eq_mul, Pm, ex_add]
        field_simp [ex_ne m w]
      rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul]
      have := hall m
      rw [← Av_const _ (Pm_diff h hd m) (Pm_per h hp m) w] at this
      unfold Av at this
      exact mul_eq_zero_of_right _ this)
    have := hD x
    rw [hD0] at this
    simpa using this.symm
  funext z
  have : z = rl (fun i => (z i).re) + fun i => I * ((z i).im : ℂ) := by
    funext i; simp only [rl, Pi.add_apply]; rw [mul_comm]; exact (re_add_im _).symm
  rw [this]; exact hz _ _
end ReciprocityTheory.ChartRestriction.G.I2.DimB
