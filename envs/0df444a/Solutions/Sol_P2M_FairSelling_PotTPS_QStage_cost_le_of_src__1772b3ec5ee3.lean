-- Prove2me | solution 1 for P2M_FairSelling_PotTPS_QStage_cost_le_of_src__1772b3ec5ee3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:04.421867+00:00
-- url     : https://prove2.me/submissions/e6ffe905-84e1-4f8b-80fd-69d0243303f1

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_slice_cost_le
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_TPS_le_two_thr
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
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : QStage G n} {i : Fin n} {g : G}
    (hb : s.bundle i = ∅) (ho : s.own i = ∅) (hrz : s.resv i = 0) (hsrc : s.src i = {g})
    (hle : s.cash i + s.pot p g ≤ p g) {j : Fin n}
    (hcash : s.cash i ≤ GeneralTPS.thr v p j) :
    s.cost v p i j ≤ 2 * GeneralTPS.thr v p j := by
  have ht := ChargeTPS.TPS_le_two_thr v p hn hp j
  have := slice_cost_le (v j) p (TPS n (v j) p) (GeneralTPS.thr v p j) g (s.cash i)
    (s.pot p g) hle hcash ht
  simp only [cost, hb, ho, hrz, hsrc, truncBundle, Finset.sum_empty, Finset.sum_singleton,
    zero_add, add_zero]
  linarith
end FairSelling.PotTPS.QStage
