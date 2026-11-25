-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_179a6d344b31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:22:18.639972+00:00
-- url     : https://prove2.me/submissions/9c71b12e-3271-486a-84f1-355fa55825e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PAffineChartTrdeg

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
open GroundTheory.Heights₂.Heights.AffineChartTrdeg
variable {F : Type} [Field F] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
omit [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.AffineChartTrdeg
theorem _root_.solution (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = algebraMap (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (Ideal.Quotient.mk P f) := by
  have h : aeval (genPt P) = (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P))).comp (Ideal.Quotient.mkₐ F P) :=
    MvPolynomial.algHom_ext fun i => by simp [genPt]
  rw [h]
  rfl
end GroundTheory.Heights₂.Heights.AffineChartTrdeg
