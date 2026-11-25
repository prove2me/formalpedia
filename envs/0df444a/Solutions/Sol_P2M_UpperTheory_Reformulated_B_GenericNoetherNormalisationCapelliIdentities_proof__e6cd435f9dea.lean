-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_GenericNoetherNormalisationCapelliIdentities_proof__e6cd435f9dea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:17:42.464558+00:00
-- url     : https://prove2.me/submissions/c784d973-4b96-45dc-9de9-1b1d62dccb09

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NoetherNormalizationChart
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PseudoDivision
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProofSimp
import Theorems.Thm_UpperTheory_exists_monic_change_of_variables
import Theorems.Thm_UpperTheory_pseudo_division


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof
theorem _root_.solution.{u} :
    GroundTheory.Heights₂.Heights.GenericNoetherNormalisation.Statement.{u} := by
  intro A _ _ n q _ hq _
  classical
  obtain ⟨f, hfq, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
  obtain ⟨e, a, ha, hlc⟩ := UpperTheory.exists_monic_change_of_variables A n f hf
  have hg : e f ≠ 0 := fun h ↦ hf (e.injective (by simpa using h))
  let π : Polynomial (MvPolynomial (Fin n) A) →ₐ[A] MvPolynomial (Fin (n + 1)) A ⧸ q :=
    (Ideal.Quotient.mkₐ A q).comp e.symm.toAlgHom
  have hπf : π (e f) = 0 := by
    simpa [π, Ideal.Quotient.eq_zero_iff_mem] using hfq
  have hsurj : Function.Surjective π :=
    (Ideal.Quotient.mkₐ_surjective A q).comp e.symm.surjective
  let z : Fin n → MvPolynomial (Fin (n + 1)) A ⧸ q :=
    fun i ↦ π (Polynomial.C (MvPolynomial.X i))
  have hz : ∀ c : MvPolynomial (Fin n) A, MvPolynomial.aeval z c = π (Polynomial.C c) := by
    intro c
    have : MvPolynomial.aeval z = π.comp (Polynomial.CAlgHom) := by
      ext i
      simp [z]
    rw [this]
    rfl
  let N := (e f).natDegree
  refine ⟨a, ha, z, (Finset.range N).image (fun j ↦ π Polynomial.X ^ j), fun d ↦ ?_⟩
  obtain ⟨p, rfl⟩ := hsurj d
  obtain ⟨k, s, r, hk, hr⟩ := UpperTheory.pseudo_division (MvPolynomial (Fin n) A) (e f) p hg
  have h1 : a ^ k • π p = π r := by
    have := congrArg π hk
    rw [map_add, map_mul π (e f), hπf, zero_mul, zero_add, hlc, map_mul, ← hz, ← map_pow,
      MvPolynomial.aeval_C, ← Algebra.smul_def] at this
    exact this
  have h2 : r = ∑ j ∈ Finset.range N, Polynomial.C (r.coeff j) * Polynomial.X ^ j := by
    rw [Polynomial.degree_eq_natDegree hg] at hr
    by_cases hr0 : r = 0
    · simp [hr0]
    · simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
        Polynomial.as_sum_range' r N ((Polynomial.natDegree_lt_iff_degree_lt hr0).mpr hr)
  refine ⟨k, fun t ↦ ∑ j ∈ Finset.range N with π Polynomial.X ^ j = t, r.coeff j, ?_⟩
  rw [h1, h2, map_sum, ← Finset.sum_fiberwise_of_maps_to (g := fun j ↦ π Polynomial.X ^ j)
    (fun j hj ↦ Finset.mem_image_of_mem _ hj), ← h2]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [map_mul, map_pow, hz, (Finset.mem_filter.mp hj).2]
end UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof
