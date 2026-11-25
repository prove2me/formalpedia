-- Prove2me | solution 1 for ReciprocityTheory.PGsh.p_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:58.813042+00:00
-- url     : https://prove2.me/submissions/d3f755c5-f45e-40ec-af23-9a0f32e20ee2

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MulIterateRootEqZero
import Theorems.Thm_ReciprocityTheory_PGsh_p_mul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
namespace ReciprocityTheory.PGsh
theorem _root_.solution : (p : WittVector p R) ∈ nonZeroDivisors (WittVector p R) := mem_nonZeroDivisors_iff.mpr
  ⟨fun x hx => p_mul_eq_zero x (by rwa [mul_comm] at hx), fun x hx => p_mul_eq_zero x hx⟩
end ReciprocityTheory.PGsh
