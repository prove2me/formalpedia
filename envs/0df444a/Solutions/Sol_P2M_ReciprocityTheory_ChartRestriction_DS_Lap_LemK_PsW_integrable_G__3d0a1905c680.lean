-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_integrable_G__3d0a1905c680
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:44.646338+00:00
-- url     : https://prove2.me/submissions/9bd5a96f-6d0d-4bab-92c6-e476ff36b95f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_G_k_2cdb220cc1dc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
variable {n : ℕ}
local notation "𝕄" => Fin n → Fin n → ℂ
local notation "MM" => Matrix (Fin n) (Fin n) ℂ
local notation "WW" => ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) × (Fin n → Fin n → ℂ)
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
theorem _root_.solution [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) {z : 𝕄}
    (hz : z ∈ Ps1.Uset ε) : Integrable (G' T μ D z) (muK ε) := by
  first
  | exact (continuous_G'k T μ D hz).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  | exact integrableOn_univ.1 ((continuous_G'k T μ D hz).continuousOn.integrableOn_compact isCompact_univ)
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
