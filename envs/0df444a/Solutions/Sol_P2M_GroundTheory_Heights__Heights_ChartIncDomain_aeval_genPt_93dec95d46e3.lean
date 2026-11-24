-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_genPt_93dec95d46e3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:57.437848+00:00
-- url     : https://prove2.me/submissions/f808300c-08f0-43af-9333-f12f732f2197

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncDomain

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
open GroundTheory.Heights₂.Heights.ChartIncDomain
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIncDomain
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (g : MvPolynomial (Fin n) F) :
    aeval (genPt I) g =
      algebraMap (MvPolynomial (Fin n) F ⧸ I) (FractionRing (MvPolynomial (Fin n) F ⧸ I))
        (Ideal.Quotient.mk I g) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F ⧸ I)]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, aeval_X, genPt]
end GroundTheory.Heights₂.Heights.ChartIncDomain
