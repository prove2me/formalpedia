-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.range_toM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:24.372812+00:00
-- url     : https://prove2.me/submissions/2100c152-23ab-423b-9716-d8d21a2e0d59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_left_inv_of_inUJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) : Set.range (fun g : UJ ε => toM g) = {g | inUJ ε g} := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact u.2
  · intro hg
    have h2 := left_inv_of_inUJ ε g hg
    have h1 : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.mp h2
    exact ⟨⟨⟨g, Jm ε * gᴴ * Jm ε, h1, h2⟩, hg⟩, rfl⟩
end ReciprocityTheory.ChartRestriction.DS.S7
