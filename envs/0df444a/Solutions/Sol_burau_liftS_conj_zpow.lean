-- Prove2me | solution 1 for burau_liftS_conj_zpow
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-10-01T04:35:07.273834+00:00
-- url     : https://prove2.me/submissions/7136d50c-dd11-419c-85aa-c89a8a54cb0c

import Definitions.Def_burau_reduced_braid_group
import Theorems.Thm_burau_liftS_sq_central

set_option autoImplicit false

namespace BurauNC

/-- `s t^n s⁻¹ = s⁻¹ t^n s` in `Q`: both sides lift the same element `Lm n`, because `s²` is
central (`liftS_sq_central`). -/
theorem liftS_conj_zpow_ (n : ℤ) :
    liftS * liftT ^ n * liftS⁻¹ = liftS⁻¹ * liftT ^ n * liftS := by
  have hc : liftS ^ 2 * liftT ^ n = liftT ^ n * liftS ^ 2 :=
    (Subgroup.mem_center_iff.mp burau_liftS_sq_central (liftT ^ n)).symm
  refine mul_left_cancel (a := liftS) ?_
  have h1 : liftS * (liftS * liftT ^ n * liftS⁻¹)
          = (liftS * liftS) * liftT ^ n * liftS⁻¹ := by group
  have h2 : liftS * (liftS⁻¹ * liftT ^ n * liftS) = liftT ^ n * liftS := by group
  rw [h1, h2, ← pow_two, hc, pow_two]
  group

end BurauNC

/-- **Conjugating `t` by `s` is symmetric.** In the lift of `Q ≅ Z/4 *_{Z/2} Z/6` one has
`s t^n s⁻¹ = s⁻¹ t^n s` for every `n : ℤ`, i.e. `s` and `s⁻¹` conjugate `t` in the same way. Both
sides are lifts of the same element (`Lm n = S⁻¹T^nS`), and `s²` being central makes the two
conjugations agree. -/
theorem solution (n : ℤ) :
    BurauNC.liftS * BurauNC.liftT ^ n * BurauNC.liftS⁻¹ =
      BurauNC.liftS⁻¹ * BurauNC.liftT ^ n * BurauNC.liftS :=
  BurauNC.liftS_conj_zpow_ n
