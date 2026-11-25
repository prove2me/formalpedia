-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.iteratedDeriv_dual_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:40.615041+00:00
-- url     : https://prove2.me/submissions/67aff26b-0a4a-4c2e-a53c-d01a98cdc28d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_IteratedDerivOrbit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_hasDerivAt_orbit


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
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (φ : H →L[ℝ] ℝ) (m : ℕ) : ∀ w : D,
    iteratedDeriv m (fun s : ℝ => φ (σ (NormedSpace.exp ((s : ℂ) • X)) (w : H))) =
      fun s : ℝ => φ (σ (NormedSpace.exp ((s : ℂ) • X)) ((((actM E X) ^ m) w : D) : H)) := by
  induction m with
  | zero => intro w; simp
  | succ m ih =>
    intro w
    rw [iteratedDeriv_succ']
    have hd : deriv (fun s : ℝ => φ (σ (NormedSpace.exp ((s : ℂ) • X)) (w : H))) =
        fun s : ℝ => φ (σ (NormedSpace.exp ((s : ℂ) • X)) ((actM E X w : D) : H)) := by
      funext s
      exact (φ.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_orbit hσ hD hX w s)).deriv
    rw [hd, ih (actM E X w), pow_succ, Module.End.mul_apply]
end ReciprocityTheory.ChartRestriction.DS
