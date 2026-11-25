-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_sum_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:24.139902+00:00
-- url     : https://prove2.me/submissions/48effd7c-2f3b-488f-993d-529fb78d0cbc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf

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
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) {ι : Type} (s : Finset ι) (f : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ i ∈ s, f i) w = ∑ i ∈ s, herm H (f i) w := by
  unfold herm; rw [Matrix.mulVec_sum, dotProduct_sum]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
