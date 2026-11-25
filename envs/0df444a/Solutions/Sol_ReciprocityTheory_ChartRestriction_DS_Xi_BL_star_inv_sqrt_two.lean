-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.star_inv_sqrt_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:12.811883+00:00
-- url     : https://prove2.me/submissions/4ef9be1b-67fa-4d6f-972d-d0095bd409fb

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
theorem _root_.solution : star ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  try push_cast
  rw [Complex.star_def, map_inv₀, Complex.conj_ofReal]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
