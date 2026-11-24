-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.torsion_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:22:51.634096+00:00
-- url     : https://prove2.me/submissions/24be61a8-0170-4caf-bc9c-059fe30a69d8

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
theorem _root_.solution (hv : v.Integers O) (n : ℕ) (a : O) (h : a * (p : O) ^ n = 0) : a = 0 := by
  have h' := congrArg (algebraMap O C) h
  rw [map_mul, map_pow, map_natCast, map_zero] at h'
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have h0 : algebraMap O C a = 0 := (mul_eq_zero.1 h').resolve_right (pow_ne_zero _ hpC)
  exact hv.hom_inj (by rw [h0, map_zero])
end ReciprocityTheory.PGsh.Ainf
