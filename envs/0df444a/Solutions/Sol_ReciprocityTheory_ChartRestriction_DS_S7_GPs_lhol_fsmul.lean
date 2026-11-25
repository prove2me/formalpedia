-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.lhol_fsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:02:32.198993+00:00
-- url     : https://prove2.me/submissions/49258a75-bdeb-46de-b00e-91e264fdd11f

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
theorem _root_.solution (c : ℂ) (g : Matrix (Fin n) (Fin n) ℂ → E) (X : Matrix (Fin n) (Fin n) ℂ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hg : DifferentiableAt ℂ g z) :
    Lhol X (fun y => c • g y) z = c • Lhol X g z := by
  show fderiv ℂ (fun y => c • g y) z (X * z) = c • fderiv ℂ g z (X * z)
  erw [fderiv_fun_const_smul hg c] <;> rfl
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
