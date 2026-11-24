-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_hh_f82467743477
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:30.825551+00:00
-- url     : https://prove2.me/submissions/34438936-3ce1-4f1e-936a-69bde0a4aa80

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
theorem _root_.solution {X : DblData R} (hX : X.Good) (p q : ℕ) (z : X.D p q) : X.h p (q + 1) (X.h p q z) = 0 := by
  have hm : X.h p q z ∈ LinearMap.ker (X.h p (q + 1)) := by
    rw [hX.rh p q]; exact LinearMap.mem_range_self _ z
  exact LinearMap.mem_ker.mp hm
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData.Good
