-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartChoice_joinFirst_splitFirst_0909c034ee7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:23.376814+00:00
-- url     : https://prove2.me/submissions/2a608b9f-c221-4cd1-8836-8739fad47f23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartChoice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartChoice
variable {F : Type} [Field F] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartChoice
theorem _root_.solution (p : MvPolynomial (Fin (e + 1) × Fin n) F) :
    joinFirst F e n (splitFirst F e n p) = p := by
  have h : (joinFirst F e n).comp (splitFirst F e n).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [joinFirst, splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [joinFirst, splitFirst, shiftVar]
  exact RingHom.congr_fun h p
end GroundTheory.Heights₂.Heights.ChartChoice
