-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.sepO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:04.647139+00:00
-- url     : https://prove2.me/submissions/30ebcc7c-92e2-42d5-83d6-f1569582aaba

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution (a : O) (h : ∀ n : ℕ, a ∈ span {(p : O) ^ (n + 1)}) : a = 0 := by
  apply IsHausdorff.haus' (I := span {(p : O)})
  intro n
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  cases n with
  | zero => simp
  | succ k => exact SModEq.zero.2 (h k)
end ReciprocityTheory.PGsh.Ainf
