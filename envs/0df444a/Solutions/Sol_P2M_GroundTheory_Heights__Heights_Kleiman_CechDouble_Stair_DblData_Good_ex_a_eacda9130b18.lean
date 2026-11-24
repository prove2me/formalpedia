-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ex_a_eacda9130b18
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:07.93567+00:00
-- url     : https://prove2.me/submissions/54718313-ab40-46c1-b7c8-6297cce32da7

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
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData.Good
namespace GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData.Good
theorem _root_.solution {X : DblData R} (hX : X.Good) (p : ℕ) {z : X.D p 0} (hz : X.h p 0 z = 0) :
    ∃ x, X.a p x = z := by
  have hm : z ∈ LinearMap.ker (X.h p 0) := LinearMap.mem_ker.mpr hz
  rw [hX.ra p] at hm
  exact LinearMap.mem_range.mp hm
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData.Good
