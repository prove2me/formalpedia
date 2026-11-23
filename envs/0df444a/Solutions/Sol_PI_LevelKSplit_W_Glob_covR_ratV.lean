-- Prove2me | solution 1 for PI.LevelKSplit.W.Glob.covR_ratV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:24.419575+00:00
-- url     : https://prove2.me/submissions/090deac9-5503-4222-a198-a220af02b1f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan

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
theorem _root_.solution (x y : Fin n → E) :
    covR R σ J x ⬝ᵥ ratV (F := F) R y = inclR R (hE σ J x y) := by
  simp only [covR, ratV, hE, Formalism.UG.hform, dotProduct, Finset.sum_mul, map_sum, map_mul]
  exact Finset.sum_comm
end PI.LevelKSplit.W.Glob
