-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.differentiable_aeval_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:12:12.810284+00:00
-- url     : https://prove2.me/submissions/d6a137e6-2876-4b75-baec-602ac49b7c2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ =>
      MvPolynomial.aeval (fun p : Fin n × Fin n => M p.1 p.2) Q) := by
  induction Q using MvPolynomial.induction_on
  next a => simp
  next p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  next p i hp =>
    have hX : Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ => M i.1 i.2) := by
      fun_prop
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul hX
end ReciprocityTheory.ChartRestriction.DS.HW
