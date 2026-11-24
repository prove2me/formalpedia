-- Prove2me | solution 1 for P2M_FairSelling_MMS2_cash_of_one_good_loss__47c1f0f02fdb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:08:45.586266+00:00
-- url     : https://prove2.me/submissions/4a44fda3-bdc1-457e-98c9-bd6674c2cecf

import Mathlib
import Definitions.Def_RequestProject_LemmaFourResidual
import Definitions.Def_RequestProject_PreliminaryPhase
import Theorems.Thm_FairSelling_MMS2_cash_of_one_good_loss

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (K S : Finset G) (e : G) (hKS : K ∪ S = {e}) (c m : ℝ) (hc : 0 ≤ c) (hm0 : 0 ≤ m)
    (hmτ : m ≤ (3 / 4 : ℝ) * MMS 3 w p) (hme : m ≤ p e) (hcm : p e ≤ c + m) :
    (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ S)) w)
      (cashPrice (Finset.univ \ (K ∪ S)) p c) := by
  rw [hKS]
  exact MMS2_cash_of_one_good_loss w p hw hp e c m hc hm0 hmτ hme hcm
end FairSelling
