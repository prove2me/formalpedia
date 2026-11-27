-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_isotropic_dual_of_skew_matrix__234181029e55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:46.284735+00:00
-- url     : https://prove2.me/submissions/59d2e33e-068c-4c12-b34c-4f5e5f37f8ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIsotropicDualOfSkewMatrix
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIsotropicDualOfSkewMatrixStatement
import Theorems.Thm_GlobalTheory_exists_isotropic_dual_of_skew_matrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (r g : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε ψ : Fin g → Fin r → ℚ), Mqᵀ = -Mq → (∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0) → (∀ i j, ψ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) → ∃ φ : Fin g → Fin r → ℚ, (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) ∧ (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) ∧ ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  first | exact @GlobalTheory.exists_isotropic_dual_of_skew_matrix | exact GlobalTheory.exists_isotropic_dual_of_skew_matrix | (intros; apply GlobalTheory.exists_isotropic_dual_of_skew_matrix <;> assumption)
end _root_.GlobalTheory.T
