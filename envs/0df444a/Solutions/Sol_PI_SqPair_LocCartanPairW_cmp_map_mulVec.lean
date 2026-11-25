-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_map_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:23:26.533935+00:00
-- url     : https://prove2.me/submissions/57a50845-ebf8-4190-96df-901eebe0b5c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair

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
theorem _root_.solution {ι : Type*} [Fintype ι] (h : Matrix ι ι R) (v : ι → R) :
    (fun i => σ ((h *ᵥ v) i)) = h.map σ *ᵥ (fun i => σ (v i)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
end PI.SqPair.LocCartanPairW
