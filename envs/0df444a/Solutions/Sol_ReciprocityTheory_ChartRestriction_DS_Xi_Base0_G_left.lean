-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.G_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:42:21.857376+00:00
-- url     : https://prove2.me/submissions/5a5f21e9-3250-4fe5-a67f-631f3b91f701

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_hpk_sq

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
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {g : Mat k 0} (hg : g ∈ GV k 0) : (Hpk k 0 * gᴴ * Hpk k 0) * g = 1 := by
  have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
  calc Hpk k 0 * gᴴ * Hpk k 0 * g = Hpk k 0 * (gᴴ * Hpk k 0 * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
