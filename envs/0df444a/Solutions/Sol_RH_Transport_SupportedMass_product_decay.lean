-- Prove2me | solution 1 for RH.Transport.SupportedMass.product_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:03.066209+00:00
-- url     : https://prove2.me/submissions/53d1a662-963e-4471-b6bb-91d929c2782d

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass

set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section
namespace RH.Transport.SupportedMass
theorem _root_.solution {ι : Type*} (J : Finset ι)
    (mass C ell : ι → ℝ) {Z : ℝ} (hZ : 0 < Z)
    (hmass : ∀ i ∈ J, 0 ≤ mass i)
    (hbound : ∀ i ∈ J, mass i ≤ C i * Z ^ (-ell i / 2)) :
    (∏ i ∈ J, mass i) ≤
      (∏ i ∈ J, C i) * Z ^ (-(∑ i ∈ J, ell i) / 2) := by
  calc
    _ ≤ ∏ i ∈ J, C i * Z ^ (-ell i / 2) :=
      Finset.prod_le_prod hmass hbound
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hZ]
      congr 2
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_neg_distrib]
end RH.Transport.SupportedMass
