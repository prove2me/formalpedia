-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_up_surj_bbe98ec75402
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:35.171866+00:00
-- url     : https://prove2.me/submissions/8b13a1d1-fc09-4f47-8396-6cdd93613325

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
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
theorem _root_.solution (X : DblData R) (n : ℕ) (w : X.shift.C n) : ∃ z, X.up n z = w := by
  have hw : (w : LinearMap.range (X.v 0 n)).1 ∈ LinearMap.range (X.v 0 n) := (w : LinearMap.range (X.v 0 n)).2
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hw
  exact ⟨z, Subtype.ext hz⟩
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
