-- Prove2me | solution 1 for PI.FT.formulaA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:12.082247+00:00
-- url     : https://prove2.me/submissions/cd52d4a6-efb6-4726-af6b-6b245e20b565

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Theorems.Thm_PI_FT_map_one_incl

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
variable (R : Type) [CommRing R] [Algebra F R]
namespace PI.FT
theorem _root_.solution {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
    {B : Matrix (Fin (M + 1)) (Fin M) E} (hLB : Lm σ J J' B * B = 1)
    (G : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) (G' : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (h : G * B.map (inclR (F := F) (E := E) R) = B.map (inclR (F := F) (E := E) R) * G') :
    G' = (Lm σ J J' B).map (inclR (F := F) (E := E) R) * G * B.map (inclR (F := F) (E := E) R) := by
  have hLB' : (Lm σ J J' B).map (inclR (F := F) (E := E) R) * B.map (inclR (F := F) (E := E) R) = 1 := by
    rw [← Matrix.map_mul, hLB, map_one_incl]
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hLB', Matrix.one_mul]
end PI.FT
