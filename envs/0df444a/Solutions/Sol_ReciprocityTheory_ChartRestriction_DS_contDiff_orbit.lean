-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.contDiff_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:43.040615+00:00
-- url     : https://prove2.me/submissions/1b6205aa-a825-462e-b760-769f453bc49c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_IteratedDerivOrbit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_hasDerivAt_orbit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_iteratedDeriv_orbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (N : ℕ) :
    ContDiff ℝ N (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [iteratedDeriv_orbit hσ hD hX v m]
  exact fun t => (hasDerivAt_orbit hσ hD hX ((actM E X ^ m) v) t).differentiableAt
end ReciprocityTheory.ChartRestriction.DS
