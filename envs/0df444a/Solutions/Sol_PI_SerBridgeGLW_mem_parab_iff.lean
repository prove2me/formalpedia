-- Prove2me | solution 1 for PI.SerBridgeGLW.mem_parab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:18:58.920774+00:00
-- url     : https://prove2.me/submissions/0f1fa10e-27bc-47e7-84e2-f5a1e0457805

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ClassFnOfIsIrrChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_BlockSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open PI PI.SerBridgeGLW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace PI.SerBridgeGLW
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (p : GL ι K) :
    p ∈ parab K b ↔ IsBlockUT K b (p : Matrix ι ι K) := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  letI : Invertible (p : Matrix ι ι K) := Units.invertible p
  have := Matrix.blockTriangular_inv_of_blockTriangular (M := (p : Matrix ι ι K)) (b := b) h
  rw [Matrix.coe_units_inv]
  exact this
end PI.SerBridgeGLW
