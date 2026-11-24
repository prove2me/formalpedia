-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_Good_ex_c_b833fd7a394e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:08.375675+00:00
-- url     : https://prove2.me/submissions/2ae0c589-3ff1-44a5-ac7a-d562005d87c7

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
theorem _root_.solution {X : DblData R} (hX : X.Good) (q : ℕ) {z : X.D 0 q} (hz : X.v 0 q z = 0) :
    ∃ y, X.c q y = z := by
  have hm : z ∈ LinearMap.ker (X.v 0 q) := LinearMap.mem_ker.mpr hz
  rw [hX.rc q] at hm
  exact LinearMap.mem_range.mp hm
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair.DblData.Good
