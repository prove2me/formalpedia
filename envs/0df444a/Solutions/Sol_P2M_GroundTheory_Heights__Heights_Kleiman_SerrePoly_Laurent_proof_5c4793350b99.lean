-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SerrePoly_Laurent_proof_5c4793350b99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:59.634434+00:00
-- url     : https://prove2.me/submissions/ef518386-c7b0-4e98-aa44-e9c38237c83b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_toL_injective_4902110fbee0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_map_piece_65c72f83e5aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_mk_e45328b2e1ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_res_6adc7ab2d94b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_injective_5250b9913735
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_deg_41b34c625bf3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SerrePoly.Laurent
theorem _root_.solution : SerrePoly.Laurent.Statement.{u} := by
  intro S _ N
  refine ⟨fun p q h => LaurentLoc.toL_injective S N (AddMonoidAlgebra.coeff_injective h),
    LaurentLoc.map_piece, LaurentLoc.iota, LaurentLoc.iota_injective, LaurentLoc.iota_res,
    LaurentLoc.iota_mk, LaurentLoc.iota_deg⟩
end SerrePoly.Laurent
end GroundTheory.Heights₂.Heights.Kleiman
