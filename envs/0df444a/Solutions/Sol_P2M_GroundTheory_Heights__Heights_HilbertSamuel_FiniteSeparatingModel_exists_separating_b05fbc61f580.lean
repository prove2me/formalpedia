-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_separating_b05fbc61f580
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:54:31.4479+00:00
-- url     : https://prove2.me/submissions/135c0b2c-65f3-4a1f-8256-60d64ec4e23a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiniteSeparatingModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsNoetherProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsLiftToZeros
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiniteSeparatingModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
variable {σ : Type} {e : ℕ}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
theorem _root_.solution [Fintype σ] (S : Finset (σ → ℂ)) (x : σ → ℂ) :
    ∃ u : MvPolynomial σ ℚ, ∀ z ∈ S, aeval z u = aeval x u → z = x := by
  classical
  let k : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let q : (σ → ℂ) → Polynomial ℂ :=
    fun z => ∑ i, Polynomial.C (z i - x i) * Polynomial.X ^ (k i : ℕ)
  have hq : ∀ z, z ≠ x → q z ≠ 0 := by
    intro z hz h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    have h1 := congrArg (fun r => Polynomial.coeff r (k i : ℕ)) h
    simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single i] at h1
    · rw [if_pos rfl] at h1
      exact hi (sub_eq_zero.mp h1)
    · intro j _ hj
      rw [if_neg]
      intro h'
      exact hj (k.injective (Fin.ext h'.symm))
    · simp
  let Q : Polynomial ℂ := ∏ z ∈ S.erase x, q z
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun z hz => hq z (Finset.ne_of_mem_erase hz)
  obtain ⟨c, hc⟩ : ∃ c : ℚ, Q.eval (c : ℂ) ≠ 0 := by
    by_contra h
    push Not at h
    apply Set.infinite_range_of_injective (Rat.cast_injective (α := ℂ))
    refine (Q.roots.toFinset.finite_toSet).subset ?_
    rintro _ ⟨c, rfl⟩
    simp [Polynomial.mem_roots hQ, h c]
  refine ⟨∑ i, C (c ^ (k i : ℕ)) * X i, fun z hz hzu => ?_⟩
  by_contra hzx
  have hev : aeval z (∑ i, C (c ^ (k i : ℕ)) * X i) - aeval x (∑ i, C (c ^ (k i : ℕ)) * X i) =
      (q z).eval (c : ℂ) := by
    simp only [map_sum, map_mul, aeval_C, aeval_X, q, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eq_ratCast (algebraMap ℚ ℂ)]
    push_cast
    ring
  rw [hzu, sub_self] at hev
  rw [Polynomial.eval_prod] at hc
  exact Finset.prod_ne_zero_iff.mp hc z (Finset.mem_erase.mpr ⟨hzx, hz⟩) hev.symm
end GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel
