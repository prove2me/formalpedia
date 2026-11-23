-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.signMatrix_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:06.370812+00:00
-- url     : https://prove2.me/submissions/91db12cc-63ad-474d-a28e-6e52770b0c5e

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
theorem _root_.solution (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS
