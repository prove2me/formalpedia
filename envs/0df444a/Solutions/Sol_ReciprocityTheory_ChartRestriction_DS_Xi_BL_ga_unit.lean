-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.ga_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:28.965218+00:00
-- url     : https://prove2.me/submissions/f06f9ee5-5234-402d-bf2f-a4f3a124d7e0

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
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (k r : ℕ) (U : Mat k r) (hU : Uᴴ * U = 1) (l : Fin (r + 1)) (Z : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => U *ᵥ Z a) = Ga k r l Z := by
  unfold Ga; simp only [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hU, one_mulVec]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
