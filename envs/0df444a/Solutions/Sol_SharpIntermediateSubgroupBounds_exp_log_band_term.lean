-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.exp_log_band_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:56.033358+00:00
-- url     : https://prove2.me/submissions/e00eb7ce-71e0-4aef-909c-8745d6e5c2de

import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Definitions.Def_SharpIntermediateSubgroupBounds_Decimal
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {q n r : ℕ} (hq : 1 < q) (hn : 0 < n) :
    Real.exp
        (Real.log (q : ℝ) * (r : ℝ) * (indexLog q n - (r : ℝ))) =
      (n : ℝ) ^ r / (q : ℝ) ^ (r * r) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : Real.log (q : ℝ) ≠ 0 := (Real.log_pos hqR).ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hexponent :
      Real.log (q : ℝ) * (r : ℝ) * (indexLog q n - (r : ℝ)) =
        (r : ℝ) * Real.log (n : ℝ) -
          ((r * r : ℕ) : ℝ) * Real.log (q : ℝ) := by
    unfold indexLog
    field_simp
    push_cast
    ring
  rw [hexponent, Real.exp_sub]
  rw [Real.exp_nat_mul, Real.exp_nat_mul]
  rw [Real.exp_log hnR, Real.exp_log (by positivity : (0 : ℝ) < q)]
end SharpIntermediateSubgroupBounds
