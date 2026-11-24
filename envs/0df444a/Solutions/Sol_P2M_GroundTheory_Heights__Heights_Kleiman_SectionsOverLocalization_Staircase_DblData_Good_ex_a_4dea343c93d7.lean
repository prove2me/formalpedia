-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ex_a_4dea343c93d7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:55.385801+00:00
-- url     : https://prove2.me/submissions/a9b663a5-bafd-4718-ae22-87a8a27e4451

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GraphEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase
attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC
variable {R : Type} [CommRing R]
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData.Good
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData.Good
theorem _root_.solution {X : DblData R} (hX : X.Good) (p : ℕ) {z : X.D p 0} (hz : X.h p 0 z = 0) :
    ∃ x, X.a p x = z := by
  have hm : z ∈ LinearMap.ker (X.h p 0) := LinearMap.mem_ker.mpr hz
  rw [hX.ra p] at hm
  exact LinearMap.mem_range.mp hm
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData.Good
