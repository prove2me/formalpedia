-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_nef_of_isVeryAmple_718fb75e12f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:19:36.857154+00:00
-- url     : https://prove2.me/submissions/1ff60cc2-03bf-4707-847a-96645d905136

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleProductPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLeadingCoeffPos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interNum_nonneg_of_veryAmple_68e58f10b840


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
open MvPolynomial Filter
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hR : GenericPointSectionInput.Statement.{u, w}) {k : Type u} [Field k] {Ω : Type w} [Field Ω]
    [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω} (L : LineBundle k x) (hL : IsVeryAmple L.toSubSystem) :
    Nef L.toSubSystem := by
  intro pp _ hW
  have h := interNum_nonneg_of_veryAmple hR 1 pp (fun _ => L) hW (fun _ => hL)
  have he : (fun _ : Fin 1 => L.toSubSystem) = ![L.toSubSystem] := by
    funext i; fin_cases i; rfl
  rwa [he] at h
end GroundTheory.Heights₂.Heights.Kleiman
