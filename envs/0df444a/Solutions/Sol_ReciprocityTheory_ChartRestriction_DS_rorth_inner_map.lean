-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rorth_inner_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:33.728586+00:00
-- url     : https://prove2.me/submissions/fcc3f21a-c4f3-481b-b9a1-3953b56e1557

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (x y : H) : inner ℂ (σ g x) (σ g y) = inner ℂ x y :=
  (LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (hσ.2.1 g hg)).inner_map_map x y
end ReciprocityTheory.ChartRestriction.DS
