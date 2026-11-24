-- Prove2me | solution 1 for P2M_FairSelling_PotTPS_QStage_pot_nonneg__175ac3e55641
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:01:59.382804+00:00
-- url     : https://prove2.me/submissions/092c29cf-9e67-41b8-a664-a3cb620c9efe

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_QStage_mem_cutSet
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}
namespace FairSelling.PotTPS.QStage
theorem _root_.solution (hp : ∀ g, 0 ≤ p g) {s : QStage G n} (hs : s.Good v p eps) (g : G) :
    0 ≤ s.pot p g := by
  classical
  by_cases hg : g ∈ s.cutSet
  · exact hs.pot_nonneg g hg
  · have hh : s.holders g = ∅ := by
      refine Finset.eq_empty_of_forall_notMem (fun i hi => ?_)
      simp only [holders, Finset.mem_filter] at hi
      exact hg (mem_cutSet hi.2)
    simp [pot, hh, hp g]
end FairSelling.PotTPS.QStage
