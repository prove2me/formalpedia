-- Prove2me | solution 1 for P2M_Formalism_GM_M_intPol_prod__f889d80e71c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:11.059968+00:00
-- url     : https://prove2.me/submissions/fa466141-0616-405c-ac7b-566daef66b09

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_P2M_Formalism_GM_M_intPol_mul__5d0d8163dde2
import Theorems.Thm_P2M_Formalism_GM_M_intPol_monomial__c4f29bf6f8d7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable {σ : Type}
namespace Formalism.GM.M
theorem _root_.solution {α : Type} (u : Finset α) (f : α → MvPolynomial σ ℚ_[p]) (h : ∀ i ∈ u, f i ∈ IntPol p σ) :
    (∏ i ∈ u, f i) ∈ IntPol p σ := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using intPol_monomial' (p := p) (σ := σ) 0
  | insert i u hi ih =>
    rw [prod_insert hi]
    exact intPol_mul' (h i (mem_insert_self _ _)) (ih fun k hk => h k (mem_insert_of_mem hk))
end Formalism.GM.M
