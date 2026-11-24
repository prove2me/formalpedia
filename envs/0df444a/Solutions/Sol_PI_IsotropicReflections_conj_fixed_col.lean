-- Prove2me | solution 1 for PI.IsotropicReflections.conj_fixed_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:42:27.949354+00:00
-- url     : https://prove2.me/submissions/5b283c04-424b-4e88-b852-cca4f142fb81

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
theorem _root_.solution {m : ℕ} (g H : Matrix (Fin m) (Fin m) ℂ) (p : Fin m)
    (hg : ∀ i, g i p = if i = p then 1 else 0) (q : Fin m) :
    (gᴴ * H * g) p q = ∑ j, H p j * g j q := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, hg, apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
end PI.IsotropicReflections
