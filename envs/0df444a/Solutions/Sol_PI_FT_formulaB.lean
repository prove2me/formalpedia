-- Prove2me | solution 1 for PI.FT.formulaB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:21.724655+00:00
-- url     : https://prove2.me/submissions/c3dd3764-6c6d-4c8b-9d6e-2f1ceb0a189a

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
    {B : Matrix (Fin (M + 1)) (Fin M) E} {x : Fin 1 → Fin (M + 1) → E} {b : E}
    (hdec : Xc x * qm σ J x b + B * Rm σ J J' B x b = 1)
    (G : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) (G' : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (hX : G * (Xc x).map (inclR (F := F) (E := E) R) = (Xc x).map (inclR (F := F) (E := E) R))
    (h : G * B.map (inclR (F := F) (E := E) R) = B.map (inclR (F := F) (E := E) R) * G') :
    G = (Xc x).map (inclR (F := F) (E := E) R) * (qm σ J x b).map (inclR (F := F) (E := E) R) +
      B.map (inclR (F := F) (E := E) R) * G' * (Rm σ J J' B x b).map (inclR (F := F) (E := E) R) := by
  have h1 : (Xc x).map (inclR (F := F) (E := E) R) * (qm σ J x b).map (inclR (F := F) (E := E) R) +
      B.map (inclR (F := F) (E := E) R) * (Rm σ J J' B x b).map (inclR (F := F) (E := E) R) = 1 := by
    have e1 : (Xc x * qm σ J x b).map (inclR (F := F) (E := E) R) =
        (Xc x).map (inclR (F := F) (E := E) R) * (qm σ J x b).map (inclR (F := F) (E := E) R) := Matrix.map_mul
    have e2 : (B * Rm σ J J' B x b).map (inclR (F := F) (E := E) R) =
        B.map (inclR (F := F) (E := E) R) * (Rm σ J J' B x b).map (inclR (F := F) (E := E) R) := Matrix.map_mul
    rw [← e1, ← e2, ← Matrix.map_add _ (map_add _), hdec, map_one_incl]
  calc G = G * 1 := (Matrix.mul_one G).symm
    _ = _ := by
      rw [← h1, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX, h]
end PI.FT
