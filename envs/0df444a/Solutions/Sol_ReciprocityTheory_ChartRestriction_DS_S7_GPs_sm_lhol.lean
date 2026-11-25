-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.sm_lhol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:18.019896+00:00
-- url     : https://prove2.me/submissions/87f520df-40bc-4a15-989b-943ba219e5ca

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
theorem _root_.solution {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ContDiffOn ℂ ∞ f V) (X : Matrix (Fin n) (Fin n) ℂ) : ContDiffOn ℂ ∞ (Lhol X f) V := by
  have h2 : ContDiffOn ℂ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => X * y) V := (mulL X).contDiff.contDiffOn
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen hV).mp hf).2.clm_apply h2
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
