-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ha0_aefa022df884
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:08.84175+00:00
-- url     : https://prove2.me/submissions/e3a15748-482c-40de-9038-07d5208a9e3a

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
theorem _root_.solution {X : DblData R} (hX : X.Good) (p : ℕ) (x : X.A p) : X.h p 0 (X.a p x) = 0 := by
  have hm : X.a p x ∈ LinearMap.ker (X.h p 0) := by
    rw [hX.ra p]; exact LinearMap.mem_range_self _ x
  exact LinearMap.mem_ker.mp hm
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData.Good
