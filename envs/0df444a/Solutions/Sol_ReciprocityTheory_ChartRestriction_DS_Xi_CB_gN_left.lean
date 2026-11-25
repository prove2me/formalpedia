-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.CB.gN_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:39.272737+00:00
-- url     : https://prove2.me/submissions/56887137-8ee1-49fe-920d-c364f05ae79e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiIntH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TLeftH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiRNonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_gN_sq

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
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.CB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.CB
theorem _root_.solution {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) : gN (κ * g) = gN g := by
  unfold gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.DS.Xi.CB
