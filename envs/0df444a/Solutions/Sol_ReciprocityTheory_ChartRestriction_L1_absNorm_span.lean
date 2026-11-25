-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.absNorm_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:01:25.465024+00:00
-- url     : https://prove2.me/submissions/31a0cc68-7fcf-4c1c-ae6a-1fd65c66783a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQuadInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModPrincNorm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_KQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (x : 𝓞 (KQ d)) (a b : ℤ)
    (h : (((x : KQ d) : ℂ)) = a + b * omegaK d) :
    4 * (Ideal.absNorm (Ideal.span {x}) : ℤ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
  have hd0 : 0 < d := by omega
  have hn := norm_KQ hd0 (x : KQ d) (a + b / 2) (b / 2) (by
    rw [h]; simp only [omegaK, sqD]; push_cast; ring)
  rw [← Algebra.coe_norm_int] at hn
  have hn' : 4 * Algebra.norm ℤ x = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
    have : (4 : ℚ) * (Algebra.norm ℤ x : ℚ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
      rw [hn]; ring
    exact_mod_cast this
  have hpos : 0 ≤ Algebra.norm ℤ x := by
    have : 0 ≤ 4 * Algebra.norm ℤ x := by
      rw [hn']
      have : 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + (d : ℤ)) = (2 * a + b) ^ 2 + d * b ^ 2 := by ring
      rw [this]; positivity
    omega
  rw [Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg hpos, hn']
end ReciprocityTheory.ChartRestriction.L1
