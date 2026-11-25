-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_exp_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:02.464902+00:00
-- url     : https://prove2.me/submissions/2e3309d6-cb54-4ed2-a9f2-5a4f6d475340

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
theorem _root_.solution {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsSelfAdjoint P)
    (hs : ∀ x ∈ spectrum ℝ P, 0 < x) : NormedSpace.exp (CFC.log P) = P := by
  have hlogsa : IsSelfAdjoint (CFC.log P) := cfc_predicate Real.log P
  rw [← CFC.real_exp_eq_normedSpace_exp hlogsa]
  show cfc Real.exp (cfc Real.log P) = P
  rw [← cfc_comp Real.exp Real.log P hP Real.continuous_exp.continuousOn
    (Real.continuousOn_log.mono fun x hx => (hs x hx).ne')]
  conv_rhs => rw [← cfc_id' ℝ P hP]
  exact cfc_congr fun x hx => Real.exp_log (hs x hx)
end ReciprocityTheory.ChartRestriction.DS.PolarDecomposition
