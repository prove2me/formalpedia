-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.v_intCast_lt_one_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:13.036633+00:00
-- url     : https://prove2.me/submissions/741b6c67-b8cf-4013-9a32-5cb2eb5fb09d

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_intCast_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution (hv : v.Integers R) (hpv : v (p : C) < 1) {n : ℤ}
    (h : (p : ℤ) ∣ n) : v (n : C) < 1 := by
  obtain ⟨m, rfl⟩ := h
  push_cast
  rw [map_mul]
  calc v (p : C) * v (m : C) ≤ v (p : C) * 1 :=
        mul_le_mul_of_nonneg_left (v_intCast_le_one hv m) zero_le'
    _ < 1 := by rw [mul_one]; exact hpv
end ReciprocityTheory.PGsh.Up.U3
