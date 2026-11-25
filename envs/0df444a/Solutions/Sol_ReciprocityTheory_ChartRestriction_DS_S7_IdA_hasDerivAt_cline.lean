-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.IdA.hasDerivAt_cline
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:46.972678+00:00
-- url     : https://prove2.me/submissions/76f383ee-9345-436b-96b6-48d932455e27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_cline_eq

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
open ReciprocityTheory.ChartRestriction.DS.S7.IdA
namespace ReciprocityTheory.ChartRestriction.DS.S7.IdA
theorem _root_.solution (k : KG ε) (a b : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    HasDerivAt (fun s : ℂ => toMK k⁻¹ * (a + s • b) * toMK k) (toMK k⁻¹ * b * toMK k) s := by
  have h := ((hasDerivAt_id s).smul_const (toMK k⁻¹ * b * toMK k)).const_add (toMK k⁻¹ * a * toMK k)
  simp only [id, one_smul] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => cline_eq k a b s)
end ReciprocityTheory.ChartRestriction.DS.S7.IdA
