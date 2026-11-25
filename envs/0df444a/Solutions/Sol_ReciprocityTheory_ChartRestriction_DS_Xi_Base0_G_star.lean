-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.G_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:06.439511+00:00
-- url     : https://prove2.me/submissions/aa2061e9-3bbe-4a55-a2ad-ba81c0b3c727

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_hpk_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_G_left

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
theorem _root_.solution {g : Mat k 0} (hg : g ∈ GV k 0) : g * Hpk k 0 * gᴴ = Hpk k 0 := by
  have h1 : g * (Hpk k 0 * gᴴ * Hpk k 0) = 1 := mul_eq_one_comm.mp (G_left hg)
  calc g * Hpk k 0 * gᴴ = g * (Hpk k 0 * gᴴ * Hpk k 0) * Hpk k 0 := by
        simp only [Matrix.mul_assoc, hpk_sq, Matrix.mul_one]
    _ = Hpk k 0 := by rw [h1, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
