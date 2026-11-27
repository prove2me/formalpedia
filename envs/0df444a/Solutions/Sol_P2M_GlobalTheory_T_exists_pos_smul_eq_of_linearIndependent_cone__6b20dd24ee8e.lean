-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_pos_smul_eq_of_linearIndependent_cone__6b20dd24ee8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:56.402464+00:00
-- url     : https://prove2.me/submissions/d24d83f4-adbc-4db9-8210-5ebd7848bb13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPosSmulEqOfLinearIndependentCone
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPosSmulEqOfLinearIndependentConeStatement
import Theorems.Thm_GlobalTheory_exists_pos_smul_eq_of_linearIndependent_cone


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {L : Type} [AddCommGroup L] {m m' : ℕ} (δ : Fin m → L) (γ : Fin m' → L) (i : Fin m) (k : ℕ)
    (a : Fin m' → ℕ), LinearIndependent ℤ δ → 0 < k → k • δ i = ∑ j, a j • γ j →
    (∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l) →
    ∃ (j : Fin m') (p r : ℕ), 0 < p ∧ 0 < r ∧ p • δ i = r • γ j := by
  first | exact @GlobalTheory.exists_pos_smul_eq_of_linearIndependent_cone | exact GlobalTheory.exists_pos_smul_eq_of_linearIndependent_cone | (intros; apply GlobalTheory.exists_pos_smul_eq_of_linearIndependent_cone <;> assumption)
end _root_.GlobalTheory.T
