-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.hasFDerivAt_psM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:43.237801+00:00
-- url     : https://prove2.me/submissions/8677d461-40f7-406b-aea9-295142f17248

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_hasFDerivAt_intG

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
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Uset ε) :
    HasFDerivAt (fun x : 𝕄 => psM T μ x)
      (((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
        ∫ k, GintD T μ z k ∂(muK ε)) z := by
  have h := (hasFDerivAt_intG T μ hz).const_smul
    ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))
  exact h
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
