-- Prove2me | solution 1 for Transcendental.exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/75dfdf51-acc2-5586-9ecc-441e3b54f099

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Transcendental_exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open Polynomial
open scoped Polynomial.Bivariate

namespace G1

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_ne_zero_and_aevalAeval_eq_zero {z : F} (hz : Transcendental K z)
    [Algebra.IsAlgebraic (Algebra.adjoin K {z}) F] (y : F) :
    ∃ P : K[X][Y], P ≠ 0 ∧ aevalAeval z y P = 0 := by
  obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin K {z}) y
  set e : K[X] ≃ₐ[K] Algebra.adjoin K {z} := Polynomial.algEquivOfTranscendental K z hz with he
  have hcoe : ∀ a : Algebra.adjoin K {z}, aeval z (e.symm a) = (a : F) := by
    intro a
    conv_rhs => rw [← e.apply_symm_apply a]
    rw [he, Polynomial.algEquivOfTranscendental_apply]
    simp
  refine ⟨Polynomial.mapAlgEquiv e.symm p, (EmbeddingLike.map_ne_zero_iff).mpr hp0, ?_⟩
  rw [aeval_def] at hp

  have key : ∀ q : (Algebra.adjoin K {z})[X],
      aevalAeval z y (Polynomial.mapAlgEquiv e.symm q) = eval₂ (algebraMap _ F) y q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add, eval₂_add, hp, hq]
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, eval₂_mul, eval₂_C, eval₂_X_pow]
      simp only [coe_mapAlgEquiv, map_C, map_X, map_mul, map_pow, aevalAeval_C, aevalAeval_Y]
      congr 1
      convert hcoe a using 2 <;> rfl
  rw [key, hp]

theorem exists_irreducible_aevalAeval_eq_zero_derivative_ne_zero [CharZero K]
    {z : F} (hz : Transcendental K z) [Algebra.IsAlgebraic (Algebra.adjoin K {z}) F] (y : F) :
    ∃ G : K[X][Y], Irreducible G ∧ aevalAeval z y G = 0 ∧ aevalAeval z y (derivative G) ≠ 0 := by
  classical

  have hex : ∃ n : ℕ, ∃ Q : K[X][Y], Q ≠ 0 ∧ aevalAeval z y Q = 0 ∧ Q.natDegree = n := by
    obtain ⟨P, hP0, hP⟩ := exists_ne_zero_and_aevalAeval_eq_zero hz y
    exact ⟨_, P, hP0, hP, rfl⟩
  obtain ⟨G₀, hG₀0, hG₀, hdeg⟩ := Nat.find_spec hex
  have hmin : ∀ Q : K[X][Y], Q ≠ 0 → aevalAeval z y Q = 0 → G₀.natDegree ≤ Q.natDegree := by
    intro Q hQ0 hQ
    rw [hdeg]
    exact Nat.find_min' hex ⟨Q, hQ0, hQ, rfl⟩

  have hinj : Function.Injective (aeval z : K[X] →ₐ[K] F) := transcendental_iff_injective.mp hz
  have haevalC : ∀ c : K[X], aevalAeval z y (C c) = aeval z c := fun c => aevalAeval_C z y c

  set G : K[X][Y] := G₀.primPart with hGdef
  have hGdeg : G.natDegree = G₀.natDegree := natDegree_primPart G₀
  have hc0 : G₀.content ≠ 0 := by rwa [Ne, content_eq_zero_iff]
  have hG : aevalAeval z y G = 0 := by
    have h1 : aevalAeval z y G₀ = aevalAeval z y (C G₀.content) * aevalAeval z y G := by
      rw [← map_mul, ← eq_C_content_mul_primPart]
    rw [hG₀, haevalC] at h1
    have h2 : aeval z G₀.content ≠ 0 := by
      intro h; exact hc0 (hinj (by simpa using h))
    exact (mul_eq_zero.mp h1.symm).resolve_left h2
  have hG0 : G ≠ 0 := by
    intro h; apply hG₀0
    rw [eq_C_content_mul_primPart G₀, ← hGdef, h, mul_zero]
  have hprim : G.IsPrimitive := isPrimitive_primPart G₀
  have hminG : ∀ Q : K[X][Y], Q ≠ 0 → aevalAeval z y Q = 0 → G.natDegree ≤ Q.natDegree := by
    intro Q hQ0 hQ; rw [hGdeg]; exact hmin Q hQ0 hQ

  have hpos : G.natDegree ≠ 0 := by
    intro h0
    have hGC : G = C (G.coeff 0) := eq_C_of_natDegree_eq_zero h0
    have : aeval z (G.coeff 0) = 0 := by rw [← haevalC, ← hGC, hG]
    have hc : G.coeff 0 = 0 := hinj (by simpa using this)
    exact hG0 (by rw [hGC, hc, map_zero])
  refine ⟨G, ?_, hG, ?_⟩
  ·
    refine irreducible_iff.mpr ⟨?_, ?_⟩
    · intro hu
      exact hpos (natDegree_eq_zero_of_isUnit hu)
    · intro a b hab
      have ha0 : a ≠ 0 := by rintro rfl; exact hG0 (by simpa using hab)
      have hb0 : b ≠ 0 := by rintro rfl; exact hG0 (by simpa using hab)
      have hdegab : G.natDegree = a.natDegree + b.natDegree := by rw [hab, natDegree_mul ha0 hb0]
      have hzero : aevalAeval z y a = 0 ∨ aevalAeval z y b = 0 := by
        rw [← mul_eq_zero, ← map_mul, ← hab, hG]
      rcases hzero with h | h
      ·
        right
        have hb : b.natDegree = 0 := by have := hminG a ha0 h; omega
        rw [eq_C_of_natDegree_eq_zero hb]
        refine (hprim (b.coeff 0) ?_).map C
        rw [hab, eq_C_of_natDegree_eq_zero hb]
        simp
      · left
        have ha : a.natDegree = 0 := by have := hminG b hb0 h; omega
        rw [eq_C_of_natDegree_eq_zero ha]
        refine (hprim (a.coeff 0) ?_).map C
        rw [hab, eq_C_of_natDegree_eq_zero ha]
        simp
  ·
    intro hder
    have hd0 : derivative G ≠ 0 := by
      intro h
      exact hpos (natDegree_eq_zero_of_derivative_eq_zero h)
    have hlt : (derivative G).natDegree < G.natDegree := natDegree_derivative_lt hpos
    have := hminG _ hd0 hder
    omega

theorem main [CharZero K] (htr : Cardinal.lift.{0} (Algebra.trdeg K F) ≤ 1)
    {z : F} (hz : Transcendental K z) (y : F) :
    ∃ G : K[X][Y], Irreducible G ∧ aevalAeval z y G = 0 ∧ aevalAeval z y (derivative G) ≠ 0 := by
  have hind : AlgebraicIndependent K ![z] := algebraicIndependent_iff_transcendental.mpr hz
  have hb : IsTranscendenceBasis K ![z] :=
    hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by simpa using htr)
  have halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range ![z])) F := hb.isAlgebraic
  rw [Matrix.range_cons_empty] at halg
  exact exists_irreducible_aevalAeval_eq_zero_derivative_ne_zero hz y

end G1

namespace G1

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalEval_map_mapRingHom_eq_aevalAeval (z y : F) (G : K[X][Y]) :
    (G.map (mapRingHom (algebraMap K F))).evalEval z y = aevalAeval z y G := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, evalEval_add, map_add, hp, hq]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      coe_mapRingHom, evalEval_mul, evalEval_pow, evalEval_C, evalEval_X, eval_map, map_mul,
      map_pow, aevalAeval_C, aevalAeval_Y, aeval_def]

end G1

theorem G1.exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero_of_trdeg_le_one
    {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
    (hF : Algebra.trdeg K F ≤ 1) {z : F} (hz : Transcendental K z) (y : F) :
    ∃ G : Polynomial (Polynomial K), Irreducible G ∧
      (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0 ∧
      ((Polynomial.derivative G).map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y ≠ 0 := by
  simp_rw [G1.evalEval_map_mapRingHom_eq_aevalAeval]
  refine G1.main ?_ hz y
  simpa [Cardinal.lift_le_one_iff] using hF

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
    (x₀ : F) [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
    {z : F} (hz : Transcendental K z) (y : F) :
    ∃ G : Polynomial (Polynomial K), Irreducible G ∧
      (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0 ∧
      ((Polynomial.derivative G).map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y ≠ 0 := by
  have h1 : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ F
  have h2 : Algebra.IsAlgebraic (Algebra.adjoin K ({x₀} : Set F)) F :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp h1
  have h3 : Algebra.trdeg K F ≤ 1 := by
    simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk K ({x₀} : Set F)
  exact G1.exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero_of_trdeg_le_one h3 hz y

#print axioms solution

end S_Transcendental_exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero
end P2MW
export P2MW.S_Transcendental_exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero (solution)
