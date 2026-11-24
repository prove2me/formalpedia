-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_up_surj_a97217a79961
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:08.251996+00:00
-- url     : https://prove2.me/submissions/4a56c674-73a8-4058-93ab-6b51ae577a98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.CechDouble
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair
attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC
variable {R : Type u} [CommRing R]
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
namespace GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
theorem _root_.solution (X : DblData R) (n : ℕ) (w : X.shift.C n) : ∃ z, X.up n z = w := by
  have hw : (w : LinearMap.range (X.v 0 n)).1 ∈ LinearMap.range (X.v 0 n) := (w : LinearMap.range (X.v 0 n)).2
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hw
  exact ⟨z, Subtype.ext hz⟩
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData
