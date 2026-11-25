-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapPs.sm_chainH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:10:50.644381+00:00
-- url     : https://prove2.me/submissions/6de6d034-3246-468e-b426-ab1698ce6331

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPs_chainH_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_sm_DH


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
open ReciprocityTheory.ChartRestriction.DS.S7.CapPs
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
local notation "𝕄" => Matrix (Fin n) (Fin n) ℂ
local notation "𝕋" => Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapPs
theorem _root_.solution : ∀ {m : ℕ} (s : Fin m → ℂ × 𝕄) {g : 𝕋 → ℂ}, ContDiffOn ℂ ∞ g (GPs.Wset n) →
    ContDiffOn ℂ ∞ (chainH s g) (GPs.Wset n)
  | 0, s, g, hg => by simpa [chainH] using hg
  | m + 1, s, g, hg => by
    rw [chainH_succ]
    show ContDiffOn ℂ ∞ (fun p => (s 0).1 • chainH _ g p + GPs.DH (s 0).2 (chainH _ g) p) _
    exact ((solution _ hg).const_smul _).add (GPs.sm_DH _ (solution _ hg))
end ReciprocityTheory.ChartRestriction.DS.S7.CapPs
