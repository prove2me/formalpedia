-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.herm_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:33.476901+00:00
-- url     : https://prove2.me/submissions/f207c52e-f6c5-4211-b15f-014ce79c79e4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne

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
theorem _root_.solution {g : Mat k 0} (hg : g ∈ GV k 0) (v w : Fin (2 * 0 + k + 1) → ℂ) :
    herm (Hpk k 0) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k 0) v w := by
  have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
  simp only [herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, hg']
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
