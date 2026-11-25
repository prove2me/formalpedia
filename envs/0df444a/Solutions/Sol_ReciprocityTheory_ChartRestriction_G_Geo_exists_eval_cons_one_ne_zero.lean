-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_eval_cons_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:10:27.640069+00:00
-- url     : https://prove2.me/submissions/94ab0658-cf5d-445a-81e5-6d953f23e7dc

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_smul_of_degree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution [Infinite k] {r : ℕ} (H : MvPolynomial (Fin (r + 1)) k)
    (d : ℕ) (hH : ∀ m ∈ H.support, Finsupp.degree m = d) (h0 : H ≠ 0) :
    ∃ lam : Fin r → k, eval (Fin.cons (1 : k) lam) H ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h0
  have hX : H * X 0 = 0 := by
    apply MvPolynomial.funext
    intro y
    rw [map_mul, eval_X, map_zero]
    by_cases hy : y 0 = 0
    · rw [hy, mul_zero]
    · have hyeq : y = y 0 • (Fin.cons (1 : k) (fun i => (y 0)⁻¹ * y i.succ) : Fin (r + 1) → k) := by
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · simp [hy]
      rw [hyeq, eval_smul_of_degree H d hH, hall, mul_zero, zero_mul]
  rcases mul_eq_zero.mp hX with h | h
  · exact h
  · exact absurd h (X_ne_zero 0)
end ReciprocityTheory.ChartRestriction.G.Geo
