-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.phi_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:36.382362+00:00
-- url     : https://prove2.me/submissions/dadb98f0-d3fc-48d3-9e10-3a3718503cf3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_herm_hpk_r
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_phi_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable (k n : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (hk : 1 ≤ k) (a b : Fin (n + 1)) :
    herm (Hpk k n) (phiV k n a) (phiV' k n b) = if a = b then 1 else 0 := by
  unfold phiV'; rw [herm_hpk_r, phi_dot k n hk]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
