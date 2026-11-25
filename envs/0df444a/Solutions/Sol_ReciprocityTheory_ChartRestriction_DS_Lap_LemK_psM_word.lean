-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.psM_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:16:13.651794+00:00
-- url     : https://prove2.me/submissions/f5f64fa9-8d7c-40b5-8136-69d1fb8dd8bd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_Fwk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_hasFDerivAt_intG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_lWord_psM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_hasFDerivAt_intG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_Uset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_posSet_subset_Uset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_compactSpace_KG


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
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution (n : ℕ) : PsMWordInterface n := by
  intro ε Λ T μ
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  refine ⟨Ps1.Uset ε, Ps1.isOpen_Uset, Ps1.posSet_subset_Uset, fun z hz k => hz k, fun D =>
    ⟨?_, fun z hz => PsW.continuous_Fwk μ D hz, fun z hz => ?_⟩⟩
  · intro z hz
    have heq : lWord D (psM T μ) =ᶠ[𝓝 z] fun x => PsW.cc T • ∫ k, PsW.G T μ D x k ∂(muK ε) :=
      Filter.eventually_of_mem (Ps1.isOpen_Uset.mem_nhds hz) fun x hx => PsW.lWord_psM T μ D x hx
    have hd : DifferentiableAt ℂ (fun x => PsW.cc T • ∫ k, PsW.G T μ D x k ∂(muK ε)) z :=
      ((PsW.hasFDerivAt_intG T μ D hz).const_smul (PsW.cc T)).differentiableAt
    exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt
  · rw [PsW.lWord_psM T μ D z hz]
    rfl
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
