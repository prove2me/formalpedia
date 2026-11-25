-- Prove2me | solution 1 for P2M_GlobalTheory_Capelli_cross_term__f82fd11a3764
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:50:35.765576+00:00
-- url     : https://prove2.me/submissions/2b47f7c8-2308-4c22-a35d-16fe8fdad848

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_pderiv_swap
import Theorems.Thm_GlobalTheory_Capelli_polar_apply
import Theorems.Thm_GlobalTheory_Capelli_cross_term
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Capelli.polar_apply

set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
namespace GlobalTheory.Capelli
theorem _root_.solution {K σ : Type*} [CommRing K] {p q n : ℕ} (z : Fin p × Fin n → σ)
    (y : Fin q × Fin n → σ) (hzy : ∀ u w, z u ≠ y w) (P : MvPolynomial σ K) :
    (∑ k, ∑ l, ∑ b, X (y (b, k)) * pderiv (y (b, l))
        (∑ a, X (z (a, k)) * pderiv (z (a, l)) P)) =
      ∑ a, ∑ b, (∑ k, X (z (a, k)) * X (y (b, k))) *
        ∑ l, pderiv (z (a, l)) (pderiv (y (b, l)) P) := by
  rw [cross_term y z (fun u w => (hzy w u).symm), Finset.sum_comm]
  simp only [mul_comm (X (y _) : MvPolynomial σ K), pderiv_swap (y _) (z _)]
end GlobalTheory.Capelli
