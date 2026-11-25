-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_chartSubst_inl_3d0d3333bcc7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:52:03.523505+00:00
-- url     : https://prove2.me/submissions/377a29f6-444e-4248-91de-1bf2f1a4f2c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel

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
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}
variable (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution (g : MvPolynomial (Fin n) F) :
    chartSubst I t e (rename Sum.inl g) = C (chartX I t e g) := by
  have h : (chartSubst I t e).comp (rename Sum.inl).toRingHom = C.comp (chartX I t e) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [chartSubst]
    · intro m
      simp [chartSubst]
  exact RingHom.congr_fun h g
end GroundTheory.Heights₂.Heights.ChartKernel
