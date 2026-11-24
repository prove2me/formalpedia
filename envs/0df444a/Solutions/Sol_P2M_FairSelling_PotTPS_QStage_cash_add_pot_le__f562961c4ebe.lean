-- Prove2me | solution 1 for P2M_FairSelling_PotTPS_QStage_cash_add_pot_le__f562961c4ebe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:01:29.08243+00:00
-- url     : https://prove2.me/submissions/90d7ac9d-2042-4576-94f7-2b8fffafc785

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
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
omit [Fintype G]
namespace FairSelling.PotTPS.QStage
theorem _root_.solution {s : QStage G n} (hcn : ∀ i, 0 ≤ s.cash i) {i : Fin n} {g : G}
    (hg : g ∈ s.src i) : s.cash i + s.pot p g ≤ p g := by
  have hmem : i ∈ s.holders g := by simp [holders, hg]
  have h : s.cash i ≤ ∑ m ∈ s.holders g, s.cash m :=
    Finset.single_le_sum (f := s.cash) (fun m _ => hcn m) hmem
  unfold pot
  linarith
end FairSelling.PotTPS.QStage
