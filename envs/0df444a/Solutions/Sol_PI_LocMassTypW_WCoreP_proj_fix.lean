-- Prove2me | solution 1 for PI.LocMassTypW.WCoreP.proj_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:56:54.964653+00:00
-- url     : https://prove2.me/submissions/d788015a-100a-4f9a-8142-db66e9167154

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_TransitiveOverLocalRings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocMassTypW PI.LocMassTypW.WCoreP
open Matrix Module
namespace PI.LocMassTypW.WCoreP
theorem _root_.solution {R : Type*} [CommRing R] {n m : ℕ} (A0 B : Matrix (Fin n) (Fin m) R)
    (L0 M : Matrix (Fin m) (Fin n) R) (h : Matrix (Fin n) (Fin n) R)
    (h1 : h * A0 = 0) (h2 : Bᵀ * h = 0) :
    (1 - Mᵀ * Bᵀ) * h * (1 - A0 * L0) = h := by
  have e1 : Mᵀ * Bᵀ * h = 0 := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero]
  have e2 : h * (1 - A0 * L0) = h := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.zero_mul, sub_zero]
  rw [Matrix.sub_mul, Matrix.one_mul, e1, sub_zero, e2]
end PI.LocMassTypW.WCoreP
