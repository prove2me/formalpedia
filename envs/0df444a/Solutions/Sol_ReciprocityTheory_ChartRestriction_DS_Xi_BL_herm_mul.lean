-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:23:06.77382+00:00
-- url     : https://prove2.me/submissions/924df30b-640f-4a43-897b-c87c6e3ca6a4

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
theorem _root_.solution (H g : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm (gᴴ * H * g) v w := by
  unfold herm; rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
