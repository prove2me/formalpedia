-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IntegralIndep_hypotheses_inhabited_7f5e28d108f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:17.663291+00:00
-- url     : https://prove2.me/submissions/21bc1ef9-0b34-4c1d-993f-4e9e34f4bf3a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_point_dim_bd96f39da953
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isFiniteProjection_point_aeed13c83c28

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace IntegralIndep
theorem _root_.solution (p : Fin 2 → ℂ) (A : Matrix (Fin 0) (Fin 2) ℂ)
    (f : (Fin 2 → ℂ) → ℝ) (hf : Measurable f) (φ : Fin 0 → (Fin 2 → ℂ) → ℝ) :
    (RingHom.ker (MvPolynomial.eval p)).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 2) ℂ ⧸ RingHom.ker (MvPolynomial.eval p)) = (0 : ℕ) ∧
      IsFiniteProjection (RingHom.ker (MvPolynomial.eval p)) A ∧ Measurable f ∧
      (∀ k, SmoothNear (zeroSet (RingHom.ker (MvPolynomial.eval p))) (φ k)) ∧
      Integrable (chartAbsDens (RingHom.ker (MvPolynomial.eval p)) A f φ) := by
  refine ⟨RingHom.ker_isPrime _, point_dim p, isFiniteProjection_point p A, hf,
    fun k => k.elim0, ?_⟩
  have hconst : chartAbsDens (RingHom.ker (MvPolynomial.eval p)) A f φ =
      fun _ => chartAbsDens (RingHom.ker (MvPolynomial.eval p)) A f φ 0 :=
    funext fun y => congrArg _ (Subsingleton.elim y 0)
  rw [hconst]
  have : IsFiniteMeasure (volume : Measure (Fin 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty (x := 0)]
    infer_instance
  exact integrable_const _
end IntegralIndep
end GroundTheory.Heights₂.Heights
