-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.norm_gso_sq_le_two_pow_mul_of_val_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:37.105717+00:00
-- url     : https://prove2.me/submissions/5ccb3018-c9eb-4f5e-a200-70d4d4311e5f

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
open Finset InnerProductSpace ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
theorem _root_.solution (b : Fin d → E) (hr : IsRed b) :
    ∀ (n : ℕ) (i j : Fin d), i.val = j.val + n → ‖gs b j‖ ^ 2 ≤ 2 ^ n * ‖gs b i‖ ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro i j h
    have hij : i = j := Fin.ext (by simpa using h)
    subst hij; simp
  | succ n ih =>
    intro i j h
    have hk : j.val + 1 < d := by have := i.isLt; omega
    have h1 := hr.2.2 ⟨j.val + 1, hk⟩ j rfl
    have h2 := ih i ⟨j.val + 1, hk⟩ (by show i.val = j.val + 1 + n; omega)
    calc ‖gs b j‖ ^ 2 ≤ 2 * ‖gs b ⟨j.val + 1, hk⟩‖ ^ 2 := h1
      _ ≤ 2 * (2 ^ n * ‖gs b i‖ ^ 2) := by linarith
      _ = 2 ^ (n + 1) * ‖gs b i‖ ^ 2 := by ring
end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
