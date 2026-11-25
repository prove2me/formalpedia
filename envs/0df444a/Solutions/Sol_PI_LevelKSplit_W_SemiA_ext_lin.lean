-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.ext_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:03.317103+00:00
-- url     : https://prove2.me/submissions/8451bc8e-abaf-4f00-8653-03f539248d5c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Theorems.Thm_P2M_PI_LevelKSplit_W_SemiA_toMatrix__lin_81c9c19a7389

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
namespace PI.LevelKSplit.W.SemiA
theorem _root_.solution {g g' : HA R σ J} (h : ∀ v, lin R σ J g v = lin R σ J g' v) : g = g' := by
  have hl : lin R σ J g = lin R σ J g' := LinearMap.ext h
  have hm := congrArg LinearMap.toMatrix' hl
  rw [toMatrix'_lin, toMatrix'_lin] at hm
  apply Subtype.ext
  apply Units.ext
  exact hm
end PI.LevelKSplit.W.SemiA
