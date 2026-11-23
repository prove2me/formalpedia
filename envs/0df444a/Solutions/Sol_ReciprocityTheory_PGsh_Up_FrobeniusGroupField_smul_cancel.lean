-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.smul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:43.632472+00:00
-- url     : https://prove2.me/submissions/275277d7-138a-49cc-ad08-9654fc860ded

import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem
import Definitions.Def_ReciprocityTheory_DualLattices_EigPowEqOne

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
theorem _root_.solution (hv : v.Integers R) {n : Type} {e : Matrix n n R} (he : e ≠ 0) {x y : R}
    (h : x • e = y • e) : x = y := by
  obtain ⟨i, j, hij⟩ : ∃ i j, e i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact he (Matrix.ext hc)
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1
  have h2 := congrArg (algebraMap R C) h1
  rw [map_mul, map_mul] at h2
  have hne : algebraMap R C (e i j) ≠ 0 := by
    intro h0
    rw [← map_zero (algebraMap R C)] at h0
    exact hij (hv.hom_inj h0)
  exact hv.hom_inj (mul_right_cancel₀ hne h2)
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
