-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_exists_monic_map_eq_X_pow_d6b90c590648
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:10.796776+00:00
-- url     : https://prove2.me/submissions/6828b9f9-43f5-4934-901b-25ee95fbc82b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCentredIntegralEquation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
theorem _root_.solution {R B K : Type*} [CommRing R] [CommRing B] [Field K] [Algebra R B]
    [Module.Finite R B] (ε : R →+* K) (κ : K →+* R) (hεκ : ∀ c, ε (κ c) = c) (x : B)
    (hx : ∀ c : K, c ≠ 0 → ∀ y : B, IsUnit (algebraMap R B (κ c) + x * y)) :
    ∃ Q : R[X], Q.Monic ∧ aeval x Q = 0 ∧ Q.map ε = X ^ Q.natDegree := by
  classical
  have : Nontrivial R := ε.domain_nontrivial
  obtain ⟨χ, hχm, hχ⟩ := (Algebra.IsIntegral.isIntegral (R := R) x)
  have hne : χ.map ε ≠ 0 := (hχm.map ε).ne_zero
  obtain ⟨u, hfac, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (χ.map ε) hne 0
  set a := (χ.map ε).rootMultiplicity 0
  have hu0 : u.coeff 0 ≠ 0 := by
    intro h
    apply hndvd
    rw [dvd_iff_isRoot, IsRoot, ← coeff_zero_eq_eval_zero, h]
  have hεκ' : ε.comp κ = RingHom.id K := RingHom.ext hεκ
  set e := χ - X ^ a * u.map κ with he
  have hemap : e.map ε = 0 := by
    rw [he, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_map, hεκ',
      Polynomial.map_id, hfac]
    simp
  set J : Ideal B := (RingHom.ker ε).map (algebraMap R B)
  have heJ : aeval x e ∈ J := by
    rw [aeval_eq_sum_range]
    refine Ideal.sum_mem _ fun k _ => ?_
    rw [Algebra.smul_def]
    refine J.mul_mem_right _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, ← coeff_map, hemap, coeff_zero]

  obtain ⟨r, hr⟩ := X_dvd_sub_C (p := u.map κ)
  have ht : IsUnit (aeval x (u.map κ)) := by
    have h1 : u.map κ = C (κ (u.coeff 0)) + X * r := by
      rw [← hr, coeff_map]; ring
    rw [h1, map_add, aeval_C, map_mul, aeval_X]
    exact hx _ hu0 _
  have hxa : x ^ a ∈ J := by
    obtain ⟨v, hv⟩ := ht
    have h2 : x ^ a * aeval x (u.map κ) = -aeval x e := by
      have := hχ
      rw [← aeval_def] at this
      rw [show χ = X ^ a * u.map κ + e by rw [he]; ring, map_add, map_mul, map_pow, aeval_X] at this
      linear_combination this
    have h3 : x ^ a = -aeval x e * ↑v⁻¹ := by
      rw [← h2, ← hv, mul_assoc, Units.mul_inv, mul_one]
    rw [h3]
    exact J.mul_mem_right _ (J.neg_mem heJ)
  set y := x ^ (a + 1)
  have hy : y ∈ J := by
    show x ^ (a + 1) ∈ J
    rw [pow_succ]; exact J.mul_mem_right _ hxa
  have hrange : LinearMap.range (LinearMap.mulLeft R y) ≤ RingHom.ker ε • ⊤ := by
    rintro _ ⟨b, rfl⟩
    rw [Ideal.smul_top_eq_map]
    exact J.mul_mem_right b hy
  obtain ⟨q, hqm, -, hqc, hq0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R (LinearMap.mulLeft R y) _ hrange
  have hqy : aeval y q = 0 := by
    have := congrArg (fun f : Module.End R B => f 1) hq0
    rw [show (LinearMap.mulLeft R y) = Algebra.lmul R B y from rfl, aeval_algHom_apply] at this
    simpa using this
  have hqmap : q.map ε = X ^ q.natDegree := by
    conv_lhs => rw [hqm.as_sum]
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum, add_eq_left]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : q.natDegree - k ≠ 0 := by have := Finset.mem_range.1 hk; omega
    have : q.coeff k ∈ RingHom.ker ε := Ideal.pow_le_self hk' (hqc k)
    rw [RingHom.mem_ker] at this
    simp [this]
  have hQm : (q.comp (X ^ (a + 1))).Monic := hqm.comp (monic_X_pow _) (by rw [natDegree_X_pow]; omega)
  have hQ : (q.comp (X ^ (a + 1))).map ε = X ^ (q.natDegree * (a + 1)) := by
    rw [Polynomial.map_comp, hqmap, Polynomial.map_pow, Polynomial.map_X, X_pow_comp, ← pow_mul, mul_comm]
  refine ⟨q.comp (X ^ (a + 1)), hQm, ?_, ?_⟩
  · rw [aeval_comp, map_pow, aeval_X]; exact hqy
  · rw [← hQm.natDegree_map ε, hQ, natDegree_X_pow]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
