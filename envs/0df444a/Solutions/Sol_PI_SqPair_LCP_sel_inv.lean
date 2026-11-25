-- Prove2me | solution 1 for PI.SqPair.LCP.sel_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:26:58.089617+00:00
-- url     : https://prove2.me/submissions/271b84d0-5a2c-4a92-975e-b3df7f0cfa28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelCore
import Theorems.Thm_PI_SqPair_LCP_sel_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [IsDomain R]
namespace PI.SqPair.LCP
theorem _root_.solution (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det) {c : R} (hc : c ≠ 0)
    (hrel : (h₁.map σ)ᵀ * A * h₁ = c • A') :
    (A'⁻¹ * (h₁.map σ)ᵀ * A) * h₁ = c • 1 ∧ h₁ * (A'⁻¹ * (h₁.map σ)ᵀ * A) = c • 1 := by
  have h1 : (A'⁻¹ * (h₁.map σ)ᵀ * A) * h₁ = c • 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ A h₁, hrel, Matrix.mul_smul,
      Matrix.nonsing_inv_mul _ hA']
  exact ⟨h1, sel_comm hc _ _ h1⟩
end PI.SqPair.LCP
