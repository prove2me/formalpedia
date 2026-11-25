-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_gram_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:35:43.329227+00:00
-- url     : https://prove2.me/submissions/5a32d55a-b017-43f8-af3f-118466242921

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair
import Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_map_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)
namespace PI.SqPair.LocCartanPairW
theorem _root_.solution {ι : Type*} [Fintype ι] (A h : Matrix ι ι R) (v w : ι → R) :
    (fun i => σ ((h *ᵥ v) i)) ⬝ᵥ (A *ᵥ (h *ᵥ w)) =
      (fun i => σ (v i)) ⬝ᵥ (((h.map σ)ᵀ * A * h) *ᵥ w) := by
  rw [cmp_map_mulVec σ h v, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec _ (h.map σ)ᵀ, Matrix.vecMul_transpose]
end PI.SqPair.LocCartanPairW
