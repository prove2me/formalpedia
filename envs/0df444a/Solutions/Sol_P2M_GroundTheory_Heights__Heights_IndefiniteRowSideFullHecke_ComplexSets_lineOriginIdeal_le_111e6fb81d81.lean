-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lineOriginIdeal_le_111e6fb81d81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:32.464644+00:00
-- url     : https://prove2.me/submissions/969b8353-e105-4aab-a0a7-1818fa29551b

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
theorem _root_.solution : lineOriginIdeal ≤ Ideal.span {(X 0 : MvPolynomial (Fin 1) ℂ)} := by
  intro q hq
  rw [lineOriginIdeal, RingHom.mem_ker, eval_zero] at hq
  have hs : Ideal.span {(X 0 : MvPolynomial (Fin 1) ℂ)} =
      Ideal.span (X '' {(0 : Fin 1)} : Set (MvPolynomial (Fin 1) ℂ)) := by
    rw [Set.image_singleton]
  rw [hs, mem_ideal_span_X_image]
  intro m hm
  refine ⟨0, rfl, fun hm0 => ?_⟩
  have hm' : m = 0 := Finsupp.ext fun i => by
    rw [Fin.fin_one_eq_zero i]
    simpa using hm0
  subst hm'
  exact (mem_support_iff.mp hm) (by rw [← constantCoeff_eq]; exact hq)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
