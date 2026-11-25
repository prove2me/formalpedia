-- Prove2me | solution 1 for PI.LevelKSplit.W.Glob.hR_ratV_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:28.266014+00:00
-- url     : https://prove2.me/submissions/231751c1-aca0-426d-8dd5-246f05e95962

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Theorems.Thm_PI_LevelKSplit_W_Glob_sigR_inclR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Glob
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
namespace PI.LevelKSplit.W.Glob
theorem _root_.solution (x : Fin n → E) (y : Fin n → R ⊗[F] E) :
    hR R σ J (ratV (F := F) R x) y = covR R σ J x ⬝ᵥ y := by
  simp only [hR, Formalism.UG.hform, covR, ratV, JR, Matrix.map_apply, sigR_inclR, dotProduct,
    map_sum, map_mul, Finset.sum_mul]
  exact Finset.sum_comm
end PI.LevelKSplit.W.Glob
