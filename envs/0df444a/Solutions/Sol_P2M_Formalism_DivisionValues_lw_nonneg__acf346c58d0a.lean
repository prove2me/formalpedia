-- Prove2me | solution 1 for P2M_Formalism_DivisionValues_lw_nonneg__acf346c58d0a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:32.032845+00:00
-- url     : https://prove2.me/submissions/7e4b7f5f-3b13-4c66-adba-8d6cb6d68334

import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsSum
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    0 ≤ lw w := by
  unfold lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
end Formalism.DivisionValues
