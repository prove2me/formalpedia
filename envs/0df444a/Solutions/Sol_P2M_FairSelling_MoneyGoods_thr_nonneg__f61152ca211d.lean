-- Prove2me | solution 1 for P2M_FairSelling_MoneyGoods_thr_nonneg__f61152ca211d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:43:23.931571+00:00
-- url     : https://prove2.me/submissions/5cdebadc-50a3-47e8-89d6-ab056438519d

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxMoney
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MoneyGoods
open GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling.MoneyGoods
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (j : Fin n) :
    0 ≤ thr v p j := thr_nonneg v p hn hp j
end FairSelling.MoneyGoods
