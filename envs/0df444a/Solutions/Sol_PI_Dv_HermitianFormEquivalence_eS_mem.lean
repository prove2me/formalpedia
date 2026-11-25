-- Prove2me | solution 1 for PI.Dv.HermitianFormEquivalence.eS_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:06.707801+00:00
-- url     : https://prove2.me/submissions/8bb43546-fe75-4892-a951-7a285353d7f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
import Theorems.Thm_PI_Dv_HermitianFormEquivalence_eS_mul
import Theorems.Thm_PI_Dv_HermitianFormEquivalence_exists_sum_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.HermitianFormEquivalence
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.HermitianFormEquivalence
theorem _root_.solution (T : GoodSet K G) (P0 : Pair K G) (hM : M1 T P0) (s : T.S) :
    ∃ n : ℕ, ∃ a b : Fin n → MonoidAlgebra K G, eS T s = ∑ i, eS T s * a i * eps P0 * b i := by
  have hp : (T.tau s).asAlgebraHom (eps P0) ≠ 0 := by
    intro h
    have := hM s
    rw [nS, h, LinearMap.range_zero, finrank_bot] at this
    exact zero_ne_one this
  obtain ⟨n, f, g, hfg⟩ := exists_sum_eq_one _ hp
  refine ⟨n, fun i => Function.surjInv (T.irr s) (f i),
    fun i => Function.surjInv (T.irr s) (g i), ?_⟩
  have h1 : (T.tau s).asAlgebraHom
      (∑ i, Function.surjInv (T.irr s) (f i) * eps P0 * Function.surjInv (T.irr s) (g i)) = 1 := by
    rw [map_sum]
    simp only [map_mul, Function.surjInv_eq (T.irr s)]
    exact hfg
  have h2 := eS_mul T s (∑ i, Function.surjInv (T.irr s) (f i) * eps P0 *
    Function.surjInv (T.irr s) (g i))
  rw [h1, ← map_one (T.tau s).asAlgebraHom, ← eS_mul, mul_one, Finset.mul_sum] at h2
  conv_lhs => rw [← h2]
  simp only [mul_assoc]
end PI.Dv.HermitianFormEquivalence
