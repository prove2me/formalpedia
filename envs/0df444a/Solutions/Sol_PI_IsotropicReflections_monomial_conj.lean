-- Prove2me | solution 1 for PI.IsotropicReflections.monomial_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:18.805722+00:00
-- url     : https://prove2.me/submissions/504a5337-d1e3-4fbb-bcc6-8ba9caad1364

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylConjugationFixedColumn_ReflectionScalarDualIsotropic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.IsotropicReflections
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {k r : ℕ}
namespace PI.IsotropicReflections
theorem _root_.solution {m : ℕ} (w H : Matrix (Fin m) (Fin m) ℂ) (σ : Fin m → Fin m) (α : Fin m → ℂ)
    (hw : ∀ i q, w i q = if i = σ q then α q else 0) (p q : Fin m) :
    (wᴴ * H * w) p q = star (α p) * H (σ p) (σ q) * α q := by
  rw [Matrix.mul_apply]
  simp_rw [hw]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, hw, apply_ite (star : ℂ → ℂ), star_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
end PI.IsotropicReflections
