-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:16:23.910199+00:00
-- url     : https://prove2.me/submissions/645cce06-707c-4710-8df9-fec148ac5aa0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_UH_left_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_UH_inv

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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 := by
  rw [UH_inv k r hg, UH_left_inv k r hg]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
