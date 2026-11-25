-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_genPt_eq_zero_iff_029d581182e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:50.590242+00:00
-- url     : https://prove2.me/submissions/f8ddd8ff-7ce2-4772-b9ea-a4a66393961b

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
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (g : MvPolynomial (Fin n) F) :
    aeval (genPt I) g = 0 ↔ g ∈ I := by
  have h : (aeval (genPt I) : MvPolynomial (Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ I)) =
      (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ I) (FractionRing (MvPolynomial (Fin n) F ⧸ I))).comp
        (Ideal.Quotient.mkₐ F I) := by
    ext j
    simp [genPt]
  have h' : aeval (genPt I) g = algebraMap (MvPolynomial (Fin n) F ⧸ I)
      (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (Ideal.Quotient.mk I g) := by
    rw [h]
    rfl
  rw [h', map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
end GroundTheory.Heights₂.Heights.ChartKernel
