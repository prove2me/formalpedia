-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.Iic_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:58:11.223624+00:00
-- url     : https://prove2.me/submissions/b90b35c8-7943-4b1b-970f-faabef3c82ab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange

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
theorem _root_.solution (n : ℕ) : Finset.Iic (0 : Fin (n + 1)) = {0} := by
  ext a
  simp [Fin.le_zero_iff]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
