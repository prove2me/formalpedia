-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA.psM_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:23.626421+00:00
-- url     : https://prove2.me/submissions/e6f5d588-d106-4312-aa93-d7db5b4b64c9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GelfandGA_continuous_conjK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GelfandGB_contDiffOn_param
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_Uset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_compactSpace_KG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiffAt_phiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_isOpen_omega


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
open ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA
local notation "𝕄" => Fin n → Fin n → ℂ
namespace ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) :
    ContDiffOn ℂ ∞ (psM T μ) (Ps1.Uset ε) := by
  have := compactSpace_KG ε
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  have : IsFiniteMeasure (muK ε) := inferInstance
  have hφ : ContDiffOn ℂ ∞ (Ps1.PhiP μ) (OmegaSet n : Set 𝕄) := fun z hz =>
    (contDiffAt_phiM μ hz).contDiffWithinAt
  have hL : Continuous (Lop T) :=
    ((ContinuousLinearMap.lsmul ℂ ℂ).flip).continuous.comp (Ps1.continuous_P T)
  have hU : IsOpen (Ps1.Uset ε : Set 𝕄) := Ps1.isOpen_Uset
  have hΩ : IsOpen (OmegaSet n : Set 𝕄) := isOpen_omega
  have h := GelfandGB.contDiffOn_param (muK ε) (conjK ε) (continuous_conjK ε) hU hΩ
    (fun x hx k => hx k) (Ps1.PhiP μ) (Lop T) hφ hL
  have h' : ContDiffOn ℂ ∞ (fun x : 𝕄 => psM T μ x) (Ps1.Uset ε : Set 𝕄) :=
    (h.const_smul ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).congr fun x _ => rfl
  exact h'
end ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA
