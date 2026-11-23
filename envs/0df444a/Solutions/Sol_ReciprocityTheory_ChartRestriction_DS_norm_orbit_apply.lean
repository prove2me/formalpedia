-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.norm_orbit_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:02.177877+00:00
-- url     : https://prove2.me/submissions/63de8cc0-fc7f-4712-b9a2-60769523b1a2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_IteratedDerivOrbit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exp_smul_mem_UJset


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
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (t : ℝ) (w : H) : ‖σ (NormedSpace.exp ((t : ℂ) • X)) w‖ = ‖w‖ :=
  hσ.2.1 _ (exp_smul_mem_UJset hX t) w
end ReciprocityTheory.ChartRestriction.DS
