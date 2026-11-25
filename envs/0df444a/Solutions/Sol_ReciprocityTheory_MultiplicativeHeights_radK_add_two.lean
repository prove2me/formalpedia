-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.radK_add_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:00:10.401529+00:00
-- url     : https://prove2.me/submissions/f7da5a5e-1684-4fe1-9e2e-eb5c54975872

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrableOn_radJ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrableOn_radK
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tendsto_radK_boundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Set Real Filter Topology
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) :
    radK (k + 2) = ((k + 1) * radK k + radJ k) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => x ^ (m + 2) * log x)
      (((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h2 : x ^ (m + 2) * x⁻¹ = x ^ (m + 1) := by
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ hx0, mul_one]
    refine ((hasDerivAt_pow (m + 2) x).mul (Real.hasDerivAt_log hx0)).congr_deriv ?_
    rw [show m + 2 - 1 = m + 1 from rfl, h2]
    push_cast
    ring
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => -(1 / 2) * exp (-x ^ 2)) (x * exp (-x ^ 2)) x := by
    intro x _
    refine (((hasDerivAt_pow 2 x).neg.exp).const_mul (-(1 / 2 : ℝ))).congr_deriv ?_
    simp only [Pi.neg_apply, show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
    ring
  have huv' : IntegrableOn ((fun x : ℝ => x ^ (m + 2) * log x) * fun x : ℝ => x * exp (-x ^ 2)) (Ioi 0) :=
    (integrableOn_radK (k := m + 3) (by omega)).congr_fun
      (fun r _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  have hu'v : IntegrableOn ((fun x : ℝ => ((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) *
      fun x : ℝ => -(1 / 2) * exp (-x ^ 2)) (Ioi 0) :=
    IntegrableOn.congr_fun (((integrableOn_radK (k := m + 1) (by omega)).const_mul (-(1 / 2) * ((m : ℝ) + 2))).add
      ((integrableOn_radJ (m + 1)).const_mul (-(1 / 2))))
      (fun r _ => by simp only [Pi.mul_apply, Pi.add_apply]; ring) measurableSet_Ioi
  have hc : Continuous (fun r : ℝ => -(1 / 2) * (r ^ (m + 1) * (r * log r) * exp (-r ^ 2))) := by
    have := Real.continuous_mul_log
    fun_prop
  have hF0 : (-(1 / 2) * ((0 : ℝ) ^ (m + 1) * (0 * log 0) * exp (-(0 : ℝ) ^ 2))) = 0 := by simp
  have h0 : Tendsto ((fun x : ℝ => x ^ (m + 2) * log x) * fun x : ℝ => -(1 / 2) * exp (-x ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [hF0] at this
    refine this.congr (fun r => ?_)
    simp only [Pi.mul_apply]
    ring
  have hinf : Tendsto ((fun x : ℝ => x ^ (m + 2) * log x) * fun x : ℝ => -(1 / 2) * exp (-x ^ 2))
      atTop (𝓝 0) :=
    (tendsto_radK_boundary m).congr (fun r => by simp only [Pi.mul_apply]; ring)
  have key : ∫ x in Ioi (0 : ℝ), x ^ (m + 2) * log x * (x * exp (-x ^ 2)) =
      0 - 0 - ∫ x in Ioi (0 : ℝ), (((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) *
        (-(1 / 2) * exp (-x ^ 2)) :=
    integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  have e1 : radK (m + 1 + 2) = ∫ x in Ioi (0 : ℝ), x ^ (m + 2) * log x * (x * exp (-x ^ 2)) := by
    rw [radK]
    congr 1
    funext x
    ring
  have e2 : (fun x : ℝ => (((m : ℝ) + 2) * x ^ (m + 1) * log x + x ^ (m + 1)) * (-(1 / 2) * exp (-x ^ 2))) =
      fun x => (-(1 / 2) * ((m : ℝ) + 2)) * (x ^ (m + 1) * log x * exp (-x ^ 2)) +
        (-(1 / 2)) * (x ^ (m + 1) * exp (-x ^ 2)) := by
    funext x
    ring
  rw [e1, key, e2, integral_add ((integrableOn_radK (k := m + 1) (by omega)).const_mul _)
    ((integrableOn_radJ (m + 1)).const_mul _), integral_const_mul, integral_const_mul]
  rw [radK, radJ]
  push_cast
  ring
end ReciprocityTheory.MultiplicativeHeights
