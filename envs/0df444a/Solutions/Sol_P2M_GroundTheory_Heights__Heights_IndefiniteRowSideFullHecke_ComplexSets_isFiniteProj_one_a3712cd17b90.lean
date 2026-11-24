-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteProj_one_a3712cd17b90
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:02.468441+00:00
-- url     : https://prove2.me/submissions/af621363-bd24-47bc-8113-9dee49770406

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal
noncomputable section
variable {n d e : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (n : ℕ) :
    IsFiniteProj (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hA : (aeval (R := ℂ) fun i : Fin n => Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial (Fin n) ℂ))
      (linForm ((1 : Matrix (Fin n) (Fin n) ℂ) i))) = Ideal.Quotient.mkₐ ℂ ⊥ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [linForm, Matrix.one_apply]
  unfold IsFiniteProj
  rw [hA]
  exact AlgHom.Finite.of_surjective _ (Ideal.Quotient.mkₐ_surjective ℂ ⊥)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
