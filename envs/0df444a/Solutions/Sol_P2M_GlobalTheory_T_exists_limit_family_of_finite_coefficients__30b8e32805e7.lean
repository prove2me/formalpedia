-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_limit_family_of_finite_coefficients__30b8e32805e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:34.949602+00:00
-- url     : https://prove2.me/submissions/4883e37f-8919-4096-a6d9-b64c1b29ee6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLimitFamilyOfFiniteCoefficients
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLimitFamilyOfFiniteCoefficientsStatement
import Theorems.Thm_GlobalTheory_exists_limit_family_of_finite_coefficients


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (σ I R : Type) [Finite σ] [Finite I] [Finite R] (F : ℕ → I → (σ →₀ ℕ) → R), ∃ G : I → (σ →₀ ℕ) → R, ∀ N M₀ : ℕ, ∃ M, M₀ ≤ M ∧ ∀ x m, m.degree ≤ N → F M x m = G x m := by
  first | exact @GlobalTheory.exists_limit_family_of_finite_coefficients | exact GlobalTheory.exists_limit_family_of_finite_coefficients | (intros; apply GlobalTheory.exists_limit_family_of_finite_coefficients <;> assumption)
end _root_.GlobalTheory.T
