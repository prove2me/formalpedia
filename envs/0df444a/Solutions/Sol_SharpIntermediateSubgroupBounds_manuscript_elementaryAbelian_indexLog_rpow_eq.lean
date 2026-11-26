-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_indexLog_rpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:01:25.783609+00:00
-- url     : https://prove2.me/submissions/93bca1a0-0dff-484f-8859-8fd375991350

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_bottom_index

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open Filter
noncomputable section
attribute [local instance] SharpIntermediateSubgroupBounds.manuscriptSubgroupIntervalFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p a : ℕ)
    [Fact p.Prime] :
    (((⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index : ℝ) ^
        (indexLog p
          (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index / 4)) =
      (p : ℝ) ^ (a * a) := by
  rw [manuscript_elementaryAbelian_bottom_index]
  have hp : (1 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp).ne'
  rw [indexLog, Nat.cast_pow, Real.log_pow]
  change ((p : ℝ) ^ (2 * a : ℕ) : ℝ) ^
      ((((2 * a : ℕ) : ℝ) * Real.log (p : ℝ) /
        Real.log (p : ℝ)) / 4) = (p : ℝ) ^ (a * a)
  rw [mul_div_cancel_right₀ _ hlog]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  rw [show ((2 * a : ℕ) : ℝ) * (((2 * a : ℕ) : ℝ) / 4) =
      ((a * a : ℕ) : ℝ) by
    push_cast
    ring]
  exact Real.rpow_natCast (p : ℝ) (a * a)
end SharpIntermediateSubgroupBounds
