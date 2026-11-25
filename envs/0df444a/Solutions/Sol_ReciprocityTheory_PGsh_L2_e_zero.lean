-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.e_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:31:16.440698+00:00
-- url     : https://prove2.me/submissions/2eb82912-e40a-400d-aa3c-7eab2b42b846

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private theorem addChar_apply_ne_zero_dual_lattices (ψ : AddChar N C) (a : N) : ψ a ≠ 0 := by
  intro h0
  have h1 : ψ a * ψ (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul]
    simp
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1
end ReciprocityTheory.PGsh.L2
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (e : H ≃ AddChar N C) (he : ∀ h h', e (h + h') = e h * e h') : e 0 = 1 := by
  have h0 := he 0 0
  rw [add_zero] at h0
  ext a
  have ha : e 0 a = e 0 a * e 0 a := by
    have := congrArg (fun ψ : AddChar N C => ψ a) h0
    simpa only [AddChar.mul_apply] using this
  rw [AddChar.one_apply]
  exact mul_left_cancel₀ (addChar_apply_ne_zero_dual_lattices (e 0) a) (by rw [mul_one]; exact ha.symm)
end ReciprocityTheory.PGsh.L2
