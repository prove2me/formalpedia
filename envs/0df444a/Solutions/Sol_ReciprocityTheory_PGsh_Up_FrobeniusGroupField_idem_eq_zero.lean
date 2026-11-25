-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.idem_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:36:44.510007+00:00
-- url     : https://prove2.me/submissions/2f145f3e-9b98-4bfd-b238-4eb09d61b112

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (hv : v.Integers R) {n : Type} [Fintype n] [DecidableEq n]
    (e : Matrix n n R) (he : e * e = e) (hm : ∀ a b, e a b ∈ mI hv) : e = 0 := by
  have hmap : e.map (res hv) = 0 := by
    ext a b; simpa [Ideal.Quotient.eq_zero_iff_mem] using hm a b
  have hdet : IsUnit (1 - e).det := by
    apply isUnit_of_not_mem hv
    intro h
    have h1 : res hv (1 - e).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h
    rw [RingHom.map_det, map_sub, map_one, RingHom.mapMatrix_apply, hmap, sub_zero,
      Matrix.det_one] at h1
    exact one_ne_zero h1
  have hu : IsUnit (1 - e) := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  exact (hu.mul_left_eq_zero).1 this
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
