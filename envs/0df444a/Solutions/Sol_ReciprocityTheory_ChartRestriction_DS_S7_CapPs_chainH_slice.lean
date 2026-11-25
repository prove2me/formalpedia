-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapPs.chainH_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:58.115297+00:00
-- url     : https://prove2.me/submissions/71e0a491-95b5-498d-86cb-81d473477147

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPs_chainL_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPs_chainH_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPs_sm_chainH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_DH_slice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_dAtW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_isOpen_kappaOpenNeighbourhood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_lhol_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_congr


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
    ∀ p ∈ GPs.Wset n, chainH s g p = chainL s (fun y => g (y, p.2)) p.1
  | 0, s, g, _, p, _ => by simp [chainH, chainL]
  | m + 1, s, g, hg, p, hp => by
    rw [chainH_succ, chainL_succ]
    show (s 0).1 • chainH _ g p + GPs.DH (s 0).2 (chainH _ g) p =
      (s 0).1 • chainL _ (fun y => g (y, p.2)) p.1 + Lhol (s 0).2 (chainL _ (fun y => g (y, p.2))) p.1
    have hS : IsOpen {y : 𝕄 | (y, p.2) ∈ GPs.Wset n} :=
      GPs.isOpen_kappaOpenNeighbourhood.preimage (continuous_id.prodMk continuous_const)
    rw [solution _ hg p hp, GPs.DH_slice _ (GPs.dAtW (sm_chainH _ hg) hp)]
    congr 1
    exact GPs.lhol_congr hS (fun y hy => solution _ hg (y, p.2) hy) _ (show (p.1, p.2) ∈ GPs.Wset n from hp)
end ReciprocityTheory.ChartRestriction.DS.S7.CapPs
