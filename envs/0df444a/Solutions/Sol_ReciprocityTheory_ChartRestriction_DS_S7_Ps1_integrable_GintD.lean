-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.integrable_GintD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:14.663898+00:00
-- url     : https://prove2.me/submissions/de0ffb39-f0a3-49f2-b831-822919a7e269

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_GintD

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
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.Ps1
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.Ps1
theorem _root_.solution [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Uset ε) : Integrable (GintD T μ x) (muK ε) := by
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  exact integrableOn_univ.mp
    ((continuous_GintD T μ hx).continuousOn.integrableOn_compact isCompact_univ)
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
