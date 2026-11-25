-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mk_ker_eval_eq_7d4f06cbd06a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:36:08.813174+00:00
-- url     : https://prove2.me/submissions/310d7028-acdb-4afd-9f9b-b9c7eadbd147

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent

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
theorem _root_.solution {n : ℕ} (p : Fin n → ℂ) (q : MvPolynomial (Fin n) ℂ) :
    Ideal.Quotient.mk (RingHom.ker (MvPolynomial.eval p)) q =
      algebraMap ℂ _ (MvPolynomial.eval p q) := by
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, RingHom.mem_ker, map_sub]
  simp
end GroundTheory.Heights₂.Heights
