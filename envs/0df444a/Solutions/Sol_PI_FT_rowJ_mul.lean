-- Prove2me | solution 1 for PI.FT.rowJ_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:23.41923+00:00
-- url     : https://prove2.me/submissions/cd16ad98-9f2d-45f8-8230-86206de54d20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
namespace PI.FT
theorem _root_.solution {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Fin 1 → Fin n → E)
    (C : Matrix (Fin n) (Fin m) E) (k : Fin m) :
    ((Matrix.of v).map σ * J * C) 0 k = hE σ J (v 0) (fun i => C i k) := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, hE, Formalism.UG.hform, Finset.sum_mul,
    mul_assoc, RingHom.coe_coe]
  first
    | rfl
    | (rw [Finset.sum_comm]; done)
    | (rw [Finset.sum_comm]
       exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    | (exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    | (simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
       rw [Finset.sum_comm]
       exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    | (simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
       exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
end PI.FT
