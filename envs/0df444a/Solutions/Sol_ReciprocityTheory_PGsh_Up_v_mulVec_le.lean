-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.v_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:34:27.836366+00:00
-- url     : https://prove2.me/submissions/e8ee3e48-5072-4434-8304-a4d3ae875493

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsUnitMinor
import Definitions.Def_ReciprocityTheory_DualLattices_SumLatInvMulVec
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec


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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {m k : Type} [Fintype k] (P : Matrix m k C) (x : k → C)
    (hP : ∀ i j, v (P i j) ≤ 1) (hx : ∀ j, v (x j) ≤ 1) (i : m) : v ((P *ᵥ x) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine v.map_sum_le fun j _ ↦ ?_
  rw [map_mul]
  exact mul_le_one₀ (hP i j) (zero_le) (hx j)
end ReciprocityTheory.PGsh.Up
