-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.continuous_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:34.530794+00:00
-- url     : https://prove2.me/submissions/fbbe39bb-5858-4c6c-8361-29d259d8f255

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB

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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
local notation "𝕄f" => Fin n → Fin n → ℂ
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution : Continuous (fun q : Matrix (Fin n) (Fin n) ℂ × KG ε => emb q.1 q.2) := by
  have hM : Continuous (fun k : KG ε => toMK k) := by
    unfold toMK toM
    first
      | fun_prop
      | exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
      | done
  exact continuous_fst.prodMk ((hM.comp continuous_snd).prodMk (hM.comp (continuous_inv.comp continuous_snd)))
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
