-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.lhol_fsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:13.822685+00:00
-- url     : https://prove2.me/submissions/7e0fff91-b8f3-452d-8141-3c33a69d34fa

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (g : ι → Matrix (Fin n) (Fin n) ℂ → E)
    (X : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hg : ∀ i ∈ s, DifferentiableAt ℂ (g i) z) :
    Lhol X (fun y => ∑ i ∈ s, g i y) z = ∑ i ∈ s, Lhol X (g i) z := by
  show fderiv ℂ (fun y => ∑ i ∈ s, g i y) z (X * z) = ∑ i ∈ s, fderiv ℂ (g i) z (X * z)
  erw [fderiv_fun_sum hg]
  exact map_sum ({ toFun := fun L => L (X * z), map_zero' := rfl, map_add' := fun _ _ => rfl } :
    (Matrix (Fin n) (Fin n) ℂ →L[ℂ] E) →+ E) _ _
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
