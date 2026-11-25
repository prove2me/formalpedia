-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_proof_f837b8440724
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:09:14.099825+00:00
-- url     : https://prove2.me/submissions/aa6d0dfa-f666-4d25-970a-b4c52cffb0f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GraphEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_equiv_8eade1ea0150

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
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
namespace Staircase
theorem _root_.solution : Staircase.Statement := by
  intro R _ D _ _ v h A _ _ dA a C _ _ dC c hvh ha hc ka ra rh kc rc rv n
  exact Staircase.DblData.equiv
    { D := D, v := v, h := h, comm := hvh, A := A, dA := dA, a := a, C := C, dC := dC, c := c }
    ⟨ha, hc, ka, ra, rh, kc, rc, rv⟩ n
end Staircase
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
