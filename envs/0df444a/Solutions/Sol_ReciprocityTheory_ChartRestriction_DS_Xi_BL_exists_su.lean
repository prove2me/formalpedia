-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.exists_su
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:57:43.099375+00:00
-- url     : https://prove2.me/submissions/1a1f1a9f-a98f-456a-9e94-134daed87a81

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
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (a : Fin (1 + r' + 1)) (ha : a.val ≠ 0) : ∃ b : Fin (r' + 1), a = su b := by
  refine ⟨⟨a.val - 1, by have := a.2; omega⟩, Fin.ext ?_⟩
  show a.val = (a.val - 1) + 1
  omega
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
