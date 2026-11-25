-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.hasSum_orbit_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:24.350628+00:00
-- url     : https://prove2.me/submissions/f0917fb2-0f78-4bc1-9189-d01dd2d7d3b5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_IteratedDerivOrbit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_norm_orbit_sub_partial_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_norm_orbit_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (a : ℕ → ℝ)
    (ha : ∀ m, ‖((((actM E X) ^ m) v : D) : H)‖ ≤ a m) (t₀ t : ℝ)
    (hs : Summable fun m : ℕ => a m * |t - t₀| ^ m / (m.factorial : ℝ)) :
    HasSum (fun m : ℕ => (((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
        σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H))
      (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) := by
  have hterm : ∀ m, ‖(((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
      σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H)‖ ≤
        a m * |t - t₀| ^ m / (m.factorial : ℝ) := by
    intro m
    rw [norm_smul, norm_orbit_apply hσ hX, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow,
      Nat.abs_cast]
    have hp : 0 ≤ |t - t₀| ^ m / (m.factorial : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left (ha m) hp
    calc |t - t₀| ^ m / (m.factorial : ℝ) * ‖((((actM E X) ^ m) v : D) : H)‖
        ≤ |t - t₀| ^ m / (m.factorial : ℝ) * a m := this
      _ = a m * |t - t₀| ^ m / (m.factorial : ℝ) := by ring
  have hsumm := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hs
  rw [hasSum_iff_tendsto_nat_of_summable_norm hsumm, ← Filter.tendsto_add_atTop_iff_nat 1,
    tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
    ((Filter.tendsto_add_atTop_iff_nat 1).2 hs.tendsto_atTop_zero)
  rw [norm_sub_rev]
  exact norm_orbit_sub_partial_le hσ hD hX v a ha t₀ t N
end ReciprocityTheory.ChartRestriction.DS
