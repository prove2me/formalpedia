-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ha0_e2d278d1ebf2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:09.173107+00:00
-- url     : https://prove2.me/submissions/31951815-7915-4227-832e-57bcff682266

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
theorem _root_.solution {X : DblData R} (hX : X.Good) (p : ℕ) (x : X.A p) : X.h p 0 (X.a p x) = 0 := by
  have hm : X.a p x ∈ LinearMap.ker (X.h p 0) := by
    rw [hX.ra p]; exact LinearMap.mem_range_self _ x
  exact LinearMap.mem_ker.mp hm
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData.Good
