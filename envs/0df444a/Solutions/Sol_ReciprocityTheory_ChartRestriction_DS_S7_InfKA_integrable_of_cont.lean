-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.integrable_of_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:46.038944+00:00
-- url     : https://prove2.me/submissions/3e7ebf7e-d4ab-4c5d-ad78-ac7d2c7ba983

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKA
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKA
theorem _root_.solution [CompactSpace (KG ε)] {E : Type*} [NormedAddCommGroup E] {f : KG ε → E}
    (hf : Continuous f) : Integrable f (muK ε) := by
  first
    | exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    | (unfold muK; exact integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ))
    | (unfold muK; exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
    | exact integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
