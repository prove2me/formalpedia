-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_eq_single1_9e84b068a51a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:30:16.654105+00:00
-- url     : https://prove2.me/submissions/4df3252e-66ac-405c-86e6-a2ad82c8e9e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassGeomDegChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
theorem _root_.solution (I : PlIdx 1 n) : I = single1 (I.1.orderEmbOfFin I.2 0) := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp I.2
  have h2 : ∀ x ∈ I.1, x = c := fun x hx => by rw [hc] at hx; exact Finset.mem_singleton.mp hx
  apply Subtype.ext
  rw [h2 _ (Finset.orderEmbOfFin_mem I.1 I.2 0)]
  exact hc
end GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
