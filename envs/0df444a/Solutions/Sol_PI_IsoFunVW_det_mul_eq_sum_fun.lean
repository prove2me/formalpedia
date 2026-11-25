-- Prove2me | solution 1 for PI.IsoFunVW.det_mul_eq_sum_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:46:46.222867+00:00
-- url     : https://prove2.me/submissions/25df06eb-3297-457b-81db-cf9ed1aa56ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Equiv
open PI PI.IsoFunVW
namespace PI.IsoFunVW
theorem _root_.solution {R : Type*} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ f : Fin m → Fin n, (∏ i, A i (f i)) * (B.submatrix f id).det := by
  have hdet : (A * B).det = (detRowAlternating : (Fin m → R) [⋀^Fin m]→ₗ[R] R)
      (fun (i : Fin m) => ∑ b : Fin n, A i b • (B b : Fin m → R)) := by
    rw [Matrix.det]; congr 1; ext i j; simp [Matrix.mul_apply, Finset.sum_apply]
  have hs := (detRowAlternating : (Fin m → R) [⋀^Fin m]→ₗ[R] R).toMultilinearMap.map_sum
    (fun (i : Fin m) (b : Fin n) => A i b • (B b : Fin m → R))
  rw [hdet]
  refine hs.trans (Finset.sum_congr rfl (fun f _ => ?_))
  have := (detRowAlternating : (Fin m → R) [⋀^Fin m]→ₗ[R] R).toMultilinearMap.map_smul_univ
    (fun i => A i (f i)) (fun i => (B (f i) : Fin m → R))
  refine this.trans ?_
  rw [smul_eq_mul]
  rfl
end PI.IsoFunVW
