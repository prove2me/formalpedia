-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.lhol_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:34.094725+00:00
-- url     : https://prove2.me/submissions/f595fb9b-8c3f-4f69-a4b3-f3406319042b

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
theorem _root_.solution {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V) {f g : Matrix (Fin n) (Fin n) ℂ → E}
    (h : Set.EqOn f g V) (X : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ V) :
    Lhol X f z = Lhol X g z := by
  show fderiv ℂ f z (X * z) = fderiv ℂ g z (X * z)
  rw [(h.eventuallyEq_of_mem (hV.mem_nhds hz)).fderiv_eq]
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
