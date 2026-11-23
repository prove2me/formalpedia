-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.one_mem_unitaryJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:38.121159+00:00
-- url     : https://prove2.me/submissions/477568fd-596f-4732-8da9-537bb75f024f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOneA

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
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
  simp
end ReciprocityTheory.ChartRestriction.DS
