-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.io_phi_su
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:07:05.736727+00:00
-- url     : https://prove2.me/submissions/94f20745-1c19-430e-9f99-fc7dbc27ee9f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_phi_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_io_lv


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
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (g : Mat k r') (a : Fin (r' + 1)) :
    ιLev k 1 r' g *ᵥ phiV k (1 + r') (su a) = liftVec k 1 r' (g *ᵥ phiV k r' a) := by
  rw [← phi_lift, io_lv]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
