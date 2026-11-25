-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.lhol_sumX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:07.284176+00:00
-- url     : https://prove2.me/submissions/b3a48966-1135-402f-a1ba-c5ab0e366c23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA

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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution {ι : Type*} (s : Finset ι) (X : ι → Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (z : Matrix (Fin n) (Fin n) ℂ) :
    Lhol (∑ i ∈ s, X i) f z = ∑ i ∈ s, Lhol (X i) f z := by
  show fderiv ℂ f z ((∑ i ∈ s, X i) * z) = ∑ i ∈ s, fderiv ℂ f z (X i * z)
  rw [Finset.sum_mul, map_sum]
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
