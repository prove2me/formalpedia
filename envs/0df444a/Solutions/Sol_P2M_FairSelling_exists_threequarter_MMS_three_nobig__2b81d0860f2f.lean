-- Prove2me | solution 1 for P2M_FairSelling_exists_threequarter_MMS_three_nobig__2b81d0860f2f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:12:27.570525+00:00
-- url     : https://prove2.me/submissions/d64dae78-df11-4931-b004-4363e0443af3

import Mathlib
import Definitions.Def_RequestProject_ConfigSplit
import Definitions.Def_RequestProject_CanonicalStrict
import Definitions.Def_RequestProject_LemmaFourResidual
import Theorems.Thm_FairSelling_lemmaFourCashSold_holds
import Theorems.Thm_FairSelling_exists_threequarter_MMS_three_nobig


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i :=
  exists_threequarter_MMS_three_nobig lemmaFourCashSold_holds v p hv hp hnobig
end FairSelling
