-- Prove2me | solution 1 for PI.FT.stab_mul_Xc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:49.311536+00:00
-- url     : https://prove2.me/submissions/bd58ce75-1f5a-4329-9f24-60b80a0fc1dd

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
variable (R : Type) [CommRing R] [Algebra F R]
namespace PI.FT
theorem _root_.solution {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
    (g : Hstab R σ J x) :
    ((HA.mat R σ J (g : HA R σ J) : GL (Fin (M + 1)) (R ⊗[F] E)) :
      Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * (Xc x).map (inclR (F := F) (E := E) R) =
      (Xc x).map (inclR (F := F) (E := E) R) := by
  have hg := g.2
  simp only [Hstab, MulAction.mem_stabilizer_iff] at hg
  delta actTup ratTup at hg
  ext i j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have h2 := congrFun (congrFun hg 0) i
  rw [Matrix.mul_apply]
  simp only [Xc, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [← h2]
  rfl
end PI.FT
