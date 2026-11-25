-- Prove2me | solution 1 for PI.LocLatEq.W.intP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:58:19.309922+00:00
-- url     : https://prove2.me/submissions/5e6452e2-267c-42f9-848e-51119dfc2a8a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_EpNontrivial
import Theorems.Thm_PI_LocLatEq_W_int_of_val
import Theorems.Thm_PI_LocLatEq_W_ep_nontrivial
import Theorems.Thm_PI_LocLatEq_W_coeff_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc Polynomial
open PI PI.LocLatEq PI.LocLatEq.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace PI.LocLatEq.W
theorem _root_.solution : IntP := by
  intro F E _ _ _ _ _ h2 sig p A a ha
  rw [A.O_def] at ha
  have := ep_nontrivial A
  by_cases hr : a ∈ (algebraMap F E).range
  · obtain ⟨f, rfl⟩ := hr
    have hf : A.ιF f ∈ 𝒪[A.Fp] := by
      rw [A.compat] at ha
      have hi : IsIntegral 𝒪[A.Fp] (A.ιF f) :=
        (isIntegral_algebraMap_iff (algebraMap A.Fp A.Ep).injective).mp ha
      exact (Valuation.integer.integers _).mem_of_integral hi
    obtain ⟨d, hd, n, hn⟩ := int_of_val A f hf
    refine ⟨d, hd, algebraMap (𝓞 F) (𝓞 E) n, ?_⟩
    change algebraMap F E (d : F) * algebraMap F E f = algebraMap F E (n : F)
    rw [← map_mul, hn]
  · have hc : ∀ i, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ n : 𝓞 F, (d : F) * (minpoly F a).coeff i = n :=
      fun i => int_of_val A _ (coeff_mem h2 A a ha hr i)
    obtain ⟨d0, hd0, n0, hn0⟩ := hc 0
    obtain ⟨d1, hd1, n1, hn1⟩ := hc 1
    have hintF : IsIntegral F a := Algebra.IsIntegral.isIntegral _
    have hdeg : (minpoly F a).natDegree = 2 := by
      have h1 : (minpoly F a).natDegree ≠ 1 := fun h => hr (minpoly.natDegree_eq_one_iff.mp h)
      have h0 := minpoly.natDegree_pos hintF
      have := minpoly.natDegree_le (A := F) a
      rw [h2] at this
      omega
    have hlead : (minpoly F a).coeff 2 = 1 := by
      have := (minpoly.monic hintF).leadingCoeff
      rwa [leadingCoeff, hdeg] at this
    have hrel : algebraMap F E ((minpoly F a).coeff 0) + algebraMap F E ((minpoly F a).coeff 1) * a
        + a ^ 2 = 0 := by
      have := minpoly.aeval F a
      rw [aeval_eq_sum_range' (n := 3) (by omega)] at this
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hlead, Algebra.smul_def,
        map_one, pow_zero, pow_one, one_mul, mul_one, zero_add] at this
      linear_combination this
    have hd : d0 * d1 ∉ p.asIdeal := fun h => (p.isPrime.mem_or_mem h).elim hd0 hd1
    have hint : IsIntegral (𝓞 F) (algebraMap F E ((d0 * d1 : 𝓞 F) : F) * a) := by
      refine ⟨X ^ 2 + C (d0 * n1) * X + C (d0 * d1 * d1 * n0), by monicity!, ?_⟩
      simp only [eval₂_add, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X]
      have e0 := congrArg (algebraMap F E) hn0
      have e1 := congrArg (algebraMap F E) hn1
      simp only [map_mul] at e0 e1
      simp only [IsScalarTower.algebraMap_apply (𝓞 F) F E, map_mul] at *
      change _ = algebraMap F E (n0 : F) at e0
      linear_combination (algebraMap F E (d0 : F) * algebraMap F E (d1 : F)) ^ 2 * hrel
        - (algebraMap F E (d0 : F) * (algebraMap F E (d0 : F) * algebraMap F E (d1 : F)) * a) * e1
        - (algebraMap F E (d0 : F) * algebraMap F E (d1 : F) ^ 2) * e0
    obtain ⟨b, hb⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 E) (R := 𝓞 F) (B := E) |>.mp hint
    refine ⟨d0 * d1, hd, b, ?_⟩
    rw [show ((b : 𝓞 E) : E) = algebraMap (𝓞 E) E b from rfl, hb]
    rfl
end PI.LocLatEq.W
