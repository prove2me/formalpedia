-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.contOn_FD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:50.660401+00:00
-- url     : https://prove2.me/submissions/964cd047-a05e-46a4-9fa3-59a7d753bf30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_isOpen_kappaOpenNeighbourhood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_continuous_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_emb_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_FD_apply

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
variable {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (T : KType ε Λ) (hg : ContDiffOn ℂ ∞ g (Wset n)) :
    ContinuousOn (fun q : Matrix (Fin n) (Fin n) ℂ × KG ε => FD T g q.1 q.2) (Ps1.Uset ε ×ˢ Set.univ) := by
  have hop : Continuous (fun k : KG ε => T.op k) := continuous_subtype_val.comp T.cont
  have hPk : Continuous (Pk T) := (hop.mul continuous_const).mul (hop.comp continuous_inv)
  rw [continuousOn_clm_apply]
  intro H
  have hc : ContinuousOn (fun q : Matrix (Fin n) (Fin n) ℂ × KG ε => fderiv ℂ g (emb q.1 q.2) (H, 0) • Pk T q.2)
      (Ps1.Uset ε ×ˢ Set.univ) :=
    (((hg.continuousOn_fderiv_of_isOpen isOpen_kappaOpenNeighbourhood (by simp)).comp continuous_emb.continuousOn
      (fun q hq => emb_mem hq.1 q.2)).clm_apply continuousOn_const).smul (hPk.comp continuous_snd).continuousOn
  refine hc.congr fun q hq => ?_
  exact FD_apply T hg q.2 (emb_mem hq.1 q.2) H
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
