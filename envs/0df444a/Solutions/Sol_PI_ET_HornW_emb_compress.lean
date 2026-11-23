-- Prove2me | solution 1 for PI.ET.HornW.emb_compress
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:16.700832+00:00
-- url     : https://prove2.me/submissions/1590ca86-2f08-4656-860a-43df1e377ac5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open PI.ET.HornW
variable {n : ℕ}
namespace PI.ET.HornW
theorem _root_.solution {k : ℕ} (hk : k ≤ n) (f : Fin n → ℂ) :
    (emb hk)ᴴ * diagonal f * emb hk = diagonal (fun i => f (Fin.castLE hk i)) := by
  ext i j
  simp only [emb, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, diagonal_apply]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, (Fin.castLE_injective hk).eq_iff]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h, h.symm]
end PI.ET.HornW
