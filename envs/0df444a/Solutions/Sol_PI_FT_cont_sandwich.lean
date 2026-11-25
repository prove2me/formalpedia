-- Prove2me | solution 1 for PI.FT.cont_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:41.970412+00:00
-- url     : https://prove2.me/submissions/594528a4-5ef8-4952-b044-c3a572ea3c97

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens
import Theorems.Thm_PI_FT_cont_mul_const

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
namespace PI.FT
theorem _root_.solution {T : Type*} [TopologicalSpace T] {m n p q : Type*} [Fintype n] [Fintype p]
    (C : Matrix m n (R ⊗[F] E)) (D : Matrix p q (R ⊗[F] E)) {f : T → Matrix n p (R ⊗[F] E)}
    (hf : Continuous f) : Continuous (fun t => C * f t * D) := by
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.mul_apply, Finset.sum_mul]
  refine continuous_finset_sum _ fun l _ => continuous_finset_sum _ fun k _ => ?_
  exact (cont_mul_const R (C i k) (D l j)).comp (hf.matrix_elem k l)
end PI.FT
