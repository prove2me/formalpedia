-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_point_dim_bd96f39da953
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:19.254066+00:00
-- url     : https://prove2.me/submissions/e2774b39-2cb8-4ca0-8cdf-7f83900359fe

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_surjective_d304bca1931e

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
theorem _root_.solution {n : ℕ} (p : Fin n → ℂ) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker (MvPolynomial.eval p)) = (0 : ℕ) := by
  have : (RingHom.ker (MvPolynomial.eval p)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (eval_surjective p)
  let := Ideal.Quotient.field (RingHom.ker (MvPolynomial.eval p))
  rw [ringKrullDim_eq_zero_of_field]
  rfl
end GroundTheory.Heights₂.Heights
