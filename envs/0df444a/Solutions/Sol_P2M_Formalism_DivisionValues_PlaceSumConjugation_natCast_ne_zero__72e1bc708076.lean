-- Prove2me | solution 1 for P2M_Formalism_DivisionValues_PlaceSumConjugation_natCast_ne_zero__72e1bc708076
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:48.690797+00:00
-- url     : https://prove2.me/submissions/3af1625c-1b3d-4bd9-a77d-348af253d3e6

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.PlaceSumConjugation
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues.PlaceSumConjugation
theorem _root_.solution {g : ℕ} (hg : 0 < g) : (g : K) ≠ 0 := by
  exact_mod_cast hg.ne'
end Formalism.DivisionValues.PlaceSumConjugation
