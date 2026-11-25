-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_tail_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:39:56.95765+00:00
-- url     : https://prove2.me/submissions/fd0d2115-473c-4a87-a49d-151bf853fc66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_dirCauchy
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_expo_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {κ : Type} (R : V → ℂ) (hR : Differentiable ℂ R) (c : ℕ) (x : Fin c → V) (hx : ∀ k, ‖x k‖ ≤ 1)
    (q : ℝ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B) (u : κ → ℝ)
    (hsum : Summable (fun a => Real.exp (-(Real.pi / 2 * q * u a ^ 2))))
    (hbd : ∀ v, ‖R v‖ ≤ B * ∑' a, Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2 - q * Real.pi * u a ^ 2 +
      2 * q * Real.pi * ‖v‖ * u a)) :
    ‖iteratedFDeriv ℂ c R 0 x‖ ≤ B * (q * (c + 1)) ^ ((c : ℝ) / 2) *
      Real.exp (5 * Real.pi * c / 2) * ∑' a, Real.exp (-(Real.pi / 2 * q * u a ^ 2)) := by
  have hc1 : (0 : ℝ) < c + 1 := by positivity
  have hqc : 0 < q * (c + 1) := mul_pos hq hc1
  set ρ := 1 / Real.sqrt (q * (c + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  set S0 := ∑' a, Real.exp (-(Real.pi / 2 * q * u a ^ 2)) with hS0
  have hS0 : 0 ≤ S0 := tsum_nonneg fun a => (Real.exp_pos _).le
  have hM : ∀ v, ‖v‖ ≤ c * ρ → ‖R v‖ ≤ B * Real.exp (5 * Real.pi * c / 2) * S0 := by
    intro v hv
    have hqt : q * ‖v‖ ^ 2 ≤ c := by
      have h1 : ‖v‖ ^ 2 ≤ (c * ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
      have h2 : (c * ρ) ^ 2 = c ^ 2 / (q * (c + 1)) := by
        rw [hρ, mul_pow, div_pow, Real.sq_sqrt hqc.le]; ring
      rw [h2] at h1
      have h3 : q * ‖v‖ ^ 2 ≤ c ^ 2 / (c + 1) := by
        calc q * ‖v‖ ^ 2 ≤ q * (c ^ 2 / (q * (c + 1))) := mul_le_mul_of_nonneg_left h1 hq.le
          _ = c ^ 2 / (c + 1) := by field_simp
      refine h3.trans ?_
      rw [div_le_iff₀ hc1]; nlinarith
    have hterm : ∀ a, Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2 - q * Real.pi * u a ^ 2 +
        2 * q * Real.pi * ‖v‖ * u a) ≤
        Real.exp (5 * Real.pi * c / 2) * Real.exp (-(Real.pi / 2 * q * u a ^ 2)) := by
      intro a
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := cab_expo_le (u := u a) hq hqt
      linarith
    have hs2 : Summable (fun a => Real.exp (5 * Real.pi * c / 2) * Real.exp (-(Real.pi / 2 * q * u a ^ 2))) :=
      hsum.mul_left _
    have hs1 : Summable (fun a => Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2 - q * Real.pi * u a ^ 2 +
        2 * q * Real.pi * ‖v‖ * u a)) :=
      Summable.of_nonneg_of_le (fun a => (Real.exp_pos _).le) hterm hs2
    refine (hbd v).trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left ?_ hB) (mul_assoc _ _ _).symm)
    calc _ ≤ ∑' a, Real.exp (5 * Real.pi * c / 2) * Real.exp (-(Real.pi / 2 * q * u a ^ 2)) :=
          hs1.tsum_le_tsum hterm hs2
      _ = _ := by rw [tsum_mul_left]
  have h := cab_dirCauchy R hR c x hx ρ _ hρ0 hM
  refine h.trans (le_of_eq ?_)
  have hr : 1 / ρ ^ c = (q * (c + 1)) ^ ((c : ℝ) / 2) := by
    rw [hρ, one_div_pow, one_div_one_div, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hqc.le]
    ring_nf
  rw [div_eq_mul_one_div, hr]; ring
end ReciprocityTheory.ChartRestriction.G.I2
