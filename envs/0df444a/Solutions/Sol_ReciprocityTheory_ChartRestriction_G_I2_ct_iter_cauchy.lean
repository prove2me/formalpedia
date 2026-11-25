-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ct_iter_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:10:25.902932+00:00
-- url     : https://prove2.me/submissions/bdf03f9f-58f1-4611-a408-d27d93b64bb9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Metric
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (F : V → ℂ) (hF : ∀ m : ℕ, ContDiff ℂ m F) (ρ M : ℝ) (hρ : 0 < ρ) :
    ∀ (k : ℕ) (x : Fin k → V) (x₀ : V), (∀ j, ‖x j‖ ≤ 1) →
    (∀ y, ‖y - x₀‖ ≤ k * ρ → ‖F y‖ ≤ M) →
    ‖iteratedFDeriv ℂ k F x₀ x‖ ≤ M / ρ ^ k
  | 0, x, x₀, _, hM => by
    have := hM x₀ (by simp)
    have hx : x = 0 := Subsingleton.elim _ _
    simpa [iteratedFDeriv_zero_apply] using this
  | k + 1, x, x₀, hx, hM => by
    set e : V := x 0 with he
    set v : Fin k → V := Fin.tail x with hv
    set A := iteratedFDeriv ℂ k F with hA
    have hD : Differentiable ℂ A :=
      (hF (k + 1)).differentiable_iteratedFDeriv (m := k)
        (by exact_mod_cast Nat.lt_succ_self k)
    set g : ℂ → ℂ := fun w => A (x₀ + w • e) v with hg
    have hpath : ∀ w0 : ℂ, HasDerivAt (fun w : ℂ => x₀ + w • e) e w0 := by
      intro w0
      have := ((hasDerivAt_id w0).smul_const e).const_add x₀
      simpa using this
    have hgd : ∀ w0 : ℂ, HasDerivAt g (fderiv ℂ A (x₀ + w0 • e) e v) w0 := by
      intro w0
      have h1 := (hD (x₀ + w0 • e)).hasFDerivAt.comp_hasDerivAt w0 (hpath w0)
      have h2 := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => V) ℂ v).hasFDerivAt.comp_hasDerivAt w0 h1
      simpa [Function.comp_def] using h2
    have hgdiff : Differentiable ℂ g := fun w0 => (hgd w0).differentiableAt
    have hderiv : deriv g 0 = iteratedFDeriv ℂ (k + 1) F x₀ x := by
      rw [(hgd 0).deriv, iteratedFDeriv_succ_apply_left, zero_smul, add_zero]
    have hsph : ∀ w ∈ sphere (0 : ℂ) ρ, ‖g w‖ ≤ M / ρ ^ k := by
      intro w hw
      have hw' : ‖w‖ = ρ := by simpa using hw
      have hwe : ‖w • e‖ ≤ ρ := by
        rw [norm_smul, hw']; simpa using mul_le_mul_of_nonneg_left (hx 0) hρ.le
      have := solution F hF ρ M hρ k v (x₀ + w • e) (fun j => hx _) (by
        intro y hy
        apply hM y
        calc ‖y - x₀‖ = ‖(y - (x₀ + w • e)) + w • e‖ := by congr 1; abel
          _ ≤ ‖y - (x₀ + w • e)‖ + ‖w • e‖ := norm_add_le _ _
          _ ≤ k * ρ + ρ := add_le_add hy hwe
          _ = ((k + 1 : ℕ) : ℝ) * ρ := by push_cast; ring)
      simpa [hg, hA, hv] using this
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hgdiff.diffContOnCl hsph
    rw [hderiv] at hc
    rw [pow_succ, ← div_div]
    exact hc
end ReciprocityTheory.ChartRestriction.G.I2
