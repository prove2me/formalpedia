-- Prove2me | solution 1 for RubinSilverberg.Psi3_eval_ne_zero_of_rsFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c26ddecd-4af7-5ea5-b3c7-0730c430e5a3

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Theorems.Thm_RubinSilverberg_rsMember_Psi3_eval_ne_zero
import Theorems.Thm_RubinSilverberg_IsKleinDatum_kleinH_ne_zero
import Theorems.Thm_RubinSilverberg_IsKleinDatum_kleinT_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_Psi3_eval_ne_zero_of_rsFamily

open Polynomial RubinSilverberg

namespace Glue

theorem pullback_row {K : Type*} [Field K] [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) {a b u₀ : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hu₀ : IsKleinDatum a b u₀) (l : K) (x : RatFunc K) :
    ((rsMember (RatFunc.C a) (RatFunc.C b) (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : RatFunc K)).Ψ₃).eval x ≠ 0 :=
  rsMember_Psi3_eval_ne_zero ζ hζ ha hb hu₀ l x
theorem syzHom_row {R : Type*} [CommRing R] (n d : R) :
    kleinTHom n d ^ 2 - kleinHHom n d ^ 3 = 1728 * kleinVHom n d ^ 5 := by
  unfold kleinTHom kleinHHom kleinVHom; ring
theorem syz_row {R : Type*} [CommRing R] (u : R) : kleinT u ^ 2 - kleinH u ^ 3 = 1728 * kleinV u ^ 5 := by
  unfold kleinT kleinH kleinV; ring
theorem kleinH_ne_row {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (h : IsKleinDatum a b u₀) (ha : a ≠ 0) :
    kleinH u₀ ≠ 0 := h.kleinH_ne_zero ha
theorem kleinT_ne_row {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (h : IsKleinDatum a b u₀) (hb : b ≠ 0) :
    kleinT u₀ ≠ 0 := h.kleinT_ne_zero hb

section maps
variable {R S : Type*} [CommRing R] [CommRing S] {Φ : Type*} [FunLike Φ R S] [RingHomClass Φ R S]
theorem map_kleinH (f : Φ) (u : R) : f (kleinH u) = kleinH (f u) := by
  simp [kleinH, map_sub, map_add, map_mul, map_pow, map_ofNat]
theorem map_kleinT (f : Φ) (u : R) : f (kleinT u) = kleinT (f u) := by
  simp [kleinT, map_sub, map_add, map_mul, map_pow, map_ofNat]
theorem map_kleinHHom (f : Φ) (n d : R) : f (kleinHHom n d) = kleinHHom (f n) (f d) := by
  simp [kleinHHom, map_sub, map_add, map_mul, map_pow, map_ofNat]
theorem map_kleinTHom (f : Φ) (n d : R) : f (kleinTHom n d) = kleinTHom (f n) (f d) := by
  simp [kleinTHom, map_sub, map_add, map_mul, map_pow, map_ofNat]
end maps

section fieldmaps
variable {K L : Type*} [Field K] [Field L] {Φ : Type*} [FunLike Φ K L] [RingHomClass Φ K L]
theorem map_rsBeta (f : Φ) (u : K) : f (rsBeta u) = rsBeta (f u) := by
  simp [rsBeta, map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat, map_kleinT]
theorem map_rsGamma (f : Φ) (u : K) : f (rsGamma u) = rsGamma (f u) := by
  simp [rsGamma, map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat, map_kleinT]
end fieldmaps

section aeval
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem rsFamilyA_eq_aeval (a u₀ l : K) (x : F) :
    rsFamilyA (algebraMap K F a) (algebraMap K F u₀) (algebraMap K F l) x =
      aeval x (C (a / kleinH u₀) *
        kleinHHom (C (rsBeta u₀ + l * u₀) * X + C u₀) (C (rsGamma u₀ + l) * X + 1)) := by
  rw [map_mul, map_kleinHHom, aeval_C]
  simp only [map_add, map_mul, aeval_C, aeval_X, map_one, rsFamilyA, rsNum, rsDen, ← map_rsBeta,
    ← map_rsGamma, ← map_kleinH, map_div₀]
  ring

theorem rsFamilyB_eq_aeval (b u₀ l : K) (x : F) :
    rsFamilyB (algebraMap K F b) (algebraMap K F u₀) (algebraMap K F l) x =
      aeval x (C (b / kleinT u₀) *
        kleinTHom (C (rsBeta u₀ + l * u₀) * X + C u₀) (C (rsGamma u₀ + l) * X + 1)) := by
  rw [map_mul, map_kleinTHom, aeval_C]
  simp only [map_add, map_mul, aeval_C, aeval_X, map_one, rsFamilyB, rsNum, rsDen, ← map_rsBeta,
    ← map_rsGamma, ← map_kleinT, map_div₀]
  ring

end aeval

section eta
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [Infinite F]

theorem map_eq_rsFamilyA_poly {a l : K} {u₀ : F} {pa : K[X]}
    (h : ∀ t : F, rsFamilyA (algebraMap K F a) u₀ (algebraMap K F l) t = (pa.map (algebraMap K F)).eval t) :
    pa.map (algebraMap K F) = C (algebraMap K F a / kleinH u₀) *
      kleinHHom (C (rsBeta u₀ + algebraMap K F l * u₀) * X + C u₀) (C (rsGamma u₀ + algebraMap K F l) * X + 1) := by
  apply Polynomial.funext
  intro t
  rw [← h t, ← coe_aeval_eq_eval, ← rsFamilyA_eq_aeval (K := F) (F := F)]
  simp

theorem map_eq_rsFamilyB_poly {b l : K} {u₀ : F} {pb : K[X]}
    (h : ∀ t : F, rsFamilyB (algebraMap K F b) u₀ (algebraMap K F l) t = (pb.map (algebraMap K F)).eval t) :
    pb.map (algebraMap K F) = C (algebraMap K F b / kleinT u₀) *
      kleinTHom (C (rsBeta u₀ + algebraMap K F l * u₀) * X + C u₀) (C (rsGamma u₀ + algebraMap K F l) * X + 1) := by
  apply Polynomial.funext
  intro t
  rw [← h t, ← coe_aeval_eq_eval, ← rsFamilyB_eq_aeval (K := F) (F := F)]
  simp

end eta

section coeff
variable {F : Type*} [Field F]

theorem coeff_linpow (p u q : F) (i j : ℕ) :
    ((C p * X + C u) ^ i * (C q * X + 1) ^ j).coeff (i + j) = p ^ i * q ^ j := by
  have h1 : (C p * X + C u).natDegree ≤ 1 := by compute_degree
  have h2 : (C q * X + (1 : F[X])).natDegree ≤ 1 := by compute_degree
  rw [coeff_mul_add_eq_of_natDegree_le (df := i) (dg := j)]
  · have e1 := coeff_pow_of_natDegree_le (m := i) h1
    have e2 := coeff_pow_of_natDegree_le (m := j) h2
    rw [mul_one] at e1 e2
    rw [e1, e2]
    simp [coeff_one]
  · exact natDegree_pow_le_of_le i h1 |>.trans (by omega)
  · exact natDegree_pow_le_of_le j h2 |>.trans (by omega)

theorem coeff_kleinHHom_lin (p u q : F) :
    (kleinHHom (C p * X + C u) (C q * X + 1)).coeff 20 = kleinHHom p q := by
  have e : ∀ i j : ℕ, i + j = 20 → ((C p * X + C u) ^ i * (C q * X + 1) ^ j).coeff 20 = p ^ i * q ^ j := by
    intro i j hij; rw [← hij]; exact coeff_linpow p u q i j
  have e20 : ((C p * X + C u) ^ 20).coeff 20 = p ^ 20 := by simpa using e 20 0 rfl
  have e0 : ((C q * X + (1 : F[X])) ^ 20).coeff 20 = q ^ 20 := by simpa using e 0 20 rfl
  simp only [kleinHHom, coeff_add, coeff_sub]
  rw [show (228 : F[X]) = C 228 from (map_ofNat C 228).symm, show (494 : F[X]) = C 494 from (map_ofNat C 494).symm]
  simp only [mul_assoc, coeff_C_mul]
  rw [e20, e0, e 15 5 rfl, e 10 10 rfl, e 5 15 rfl]

theorem coeff_kleinTHom_lin (p u q : F) :
    (kleinTHom (C p * X + C u) (C q * X + 1)).coeff 30 = kleinTHom p q := by
  have e : ∀ i j : ℕ, i + j = 30 → ((C p * X + C u) ^ i * (C q * X + 1) ^ j).coeff 30 = p ^ i * q ^ j := by
    intro i j hij; rw [← hij]; exact coeff_linpow p u q i j
  have e30 : ((C p * X + C u) ^ 30).coeff 30 = p ^ 30 := by simpa using e 30 0 rfl
  have e0 : ((C q * X + (1 : F[X])) ^ 30).coeff 30 = q ^ 30 := by simpa using e 0 30 rfl
  simp only [kleinTHom, coeff_add, coeff_sub]
  rw [show (522 : F[X]) = C 522 from (map_ofNat C 522).symm, show (10005 : F[X]) = C 10005 from (map_ofNat C 10005).symm]
  simp only [mul_assoc, coeff_C_mul]
  rw [e30, e0, e 25 5 rfl, e 20 10 rfl, e 10 20 rfl, e 5 25 rfl]

end coeff

section disc
variable {K F : Type*} [Field K] [Field F] [CharZero F] [Algebra K F]

omit [CharZero F] in
private theorem infinite_F [CharZero F] : Infinite F := Infinite.of_injective _ Nat.cast_injective

theorem disc_coeff_ne_zero {a b l : K} {u₀ : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hu₀ : IsKleinDatum (algebraMap K F a) (algebraMap K F b) u₀)
    (hV : kleinVHom (rsBeta u₀ + algebraMap K F l * u₀) (rsGamma u₀ + algebraMap K F l) ≠ 0)
    {pa pb : K[X]}
    (hpa : ∀ t : F, rsFamilyA (algebraMap K F a) u₀ (algebraMap K F l) t = (pa.map (algebraMap K F)).eval t)
    (hpb : ∀ t : F, rsFamilyB (algebraMap K F b) u₀ (algebraMap K F l) t = (pb.map (algebraMap K F)).eval t) :
    4 * pa.coeff 20 ^ 3 + 27 * pb.coeff 30 ^ 2 ≠ 0 := by
  haveI := infinite_F (F := F)
  set A := algebraMap K F a
  set B := algebraMap K F b
  set L := algebraMap K F l
  have hA : A ≠ 0 := (_root_.map_ne_zero _).mpr ha
  have hB : B ≠ 0 := (_root_.map_ne_zero _).mpr hb
  have hH0 := kleinH_ne_row hu₀ hA
  have hT0 := kleinT_ne_row hu₀ hB
  have hrel : 27 * B ^ 2 * kleinH u₀ ^ 3 + 4 * A ^ 3 * kleinT u₀ ^ 2 = 0 := by
    linear_combination hu₀.1 + 4 * A ^ 3 * syz_row u₀
  set p := rsBeta u₀ + L * u₀
  set q := rsGamma u₀ + L
  have h20 : algebraMap K F (pa.coeff 20) = A / kleinH u₀ * kleinHHom p q := by
    rw [← coeff_map, map_eq_rsFamilyA_poly hpa, coeff_C_mul, coeff_kleinHHom_lin]
  have h30 : algebraMap K F (pb.coeff 30) = B / kleinT u₀ * kleinTHom p q := by
    rw [← coeff_map, map_eq_rsFamilyB_poly hpb, coeff_C_mul, coeff_kleinTHom_lin]
  intro h0
  have h1 := congrArg (algebraMap K F) h0
  rw [map_add, map_mul, map_mul, map_pow, map_pow, h20, h30, map_ofNat, map_ofNat, map_zero] at h1
  have hsyz := syzHom_row p q

  have h2 : 4 * A ^ 3 * kleinT u₀ ^ 2 * (kleinHHom p q ^ 3 - kleinTHom p q ^ 2) = 0 := by
    field_simp at h1
    linear_combination h1 - kleinTHom p q ^ 2 * hrel
  rw [show kleinHHom p q ^ 3 - kleinTHom p q ^ 2 = -(1728 * kleinVHom p q ^ 5) by linear_combination -hsyz] at h2
  have : kleinVHom p q ^ 5 = 0 := by
    have h3 : (4 * A ^ 3 * kleinT u₀ ^ 2 * 1728) * kleinVHom p q ^ 5 = 0 := by linear_combination -h2
    exact (mul_eq_zero.mp h3).resolve_left
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hA)) (pow_ne_zero 2 hT0)) (by norm_num))
  exact hV (pow_eq_zero_iff (by norm_num) |>.mp this)

end disc

section dorge
variable {K F : Type*} [Field K] [Field F] [CharZero F] [IsAlgClosed F] [Algebra K F]

omit [IsAlgClosed F] [Algebra K F] in
private theorem infinite_F' : Infinite F := Infinite.of_injective _ Nat.cast_injective

omit [Algebra K F] in
theorem exists_prim5 : ∃ ζ : F, IsPrimitiveRoot ζ 5 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (cyclotomic 5 F) (by
    rw [degree_cyclotomic, Nat.totient_prime (by decide : Nat.Prime 5)]; norm_num)
  exact ⟨z, isRoot_cyclotomic_iff.mp hz⟩

theorem Psi3_eval_ne_zero_of_rsFamily_aux {a b l : K} {u₀ : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hu₀ : IsKleinDatum (algebraMap K F a) (algebraMap K F b) u₀) {pa pb : K[X]}
    (hpa : ∀ t : F, rsFamilyA (algebraMap K F a) u₀ (algebraMap K F l) t = (pa.map (algebraMap K F)).eval t)
    (hpb : ∀ t : F, rsFamilyB (algebraMap K F b) u₀ (algebraMap K F l) t = (pb.map (algebraMap K F)).eval t)
    (g : K[X]) : ((⟨0, 0, 0, pa, pb⟩ : WeierstrassCurve K[X]).Ψ₃).eval g ≠ 0 := by
  haveI := infinite_F' (F := F)
  obtain ⟨ζ, hζ⟩ := exists_prim5 (F := F)
  set A := algebraMap K F a
  set B := algebraMap K F b
  set L := algebraMap K F l
  have hA : A ≠ 0 := (_root_.map_ne_zero _).mpr ha
  have hB : B ≠ 0 := (_root_.map_ne_zero _).mpr hb

  set j : K[X] →+* RatFunc F := (algebraMap F[X] (RatFunc F)).comp (mapRingHom (algebraMap K F)) with hj
  have hjinj : Function.Injective j :=
    (IsFractionRing.injective F[X] (RatFunc F)).comp (map_injective _ (algebraMap K F).injective)
  have hjpa : j pa = rsFamilyA (RatFunc.C A) (RatFunc.C u₀) (RatFunc.C L) RatFunc.X := by
    rw [hj, RingHom.comp_apply, coe_mapRingHom, map_eq_rsFamilyA_poly hpa,
      ← RatFunc.aeval_X_left_eq_algebraMap, ← RatFunc.algebraMap_eq_C, ← rsFamilyA_eq_aeval]
  have hjpb : j pb = rsFamilyB (RatFunc.C B) (RatFunc.C u₀) (RatFunc.C L) RatFunc.X := by
    rw [hj, RingHom.comp_apply, coe_mapRingHom, map_eq_rsFamilyB_poly hpb,
      ← RatFunc.aeval_X_left_eq_algebraMap, ← RatFunc.algebraMap_eq_C, ← rsFamilyB_eq_aeval]
  have hmap : (⟨0, 0, 0, pa, pb⟩ : WeierstrassCurve K[X]).map j =
      rsMember (RatFunc.C A) (RatFunc.C B) (RatFunc.C u₀) (RatFunc.C L) RatFunc.X := by
    simp only [WeierstrassCurve.map, map_zero, hjpa, hjpb, rsMember]
  intro h0
  have h1 : (((⟨0, 0, 0, pa, pb⟩ : WeierstrassCurve K[X]).map j).Ψ₃).eval (j g) = 0 := by
    rw [WeierstrassCurve.map_Ψ₃, eval_map, eval₂_at_apply, h0, map_zero]
  rw [hmap] at h1
  exact pullback_row ζ hζ hA hB hu₀ L (j g) h1

end dorge

end Glue

open RubinSilverberg in

theorem solution {K F : Type*} [Field K] [Field F] [CharZero F] [IsAlgClosed F] [Algebra K F] {a b l : K} {u₀ : F} (ha : a ≠ 0) (hb : b ≠ 0) (hu₀ : IsKleinDatum (algebraMap K F a) (algebraMap K F b) u₀) {pa pb : Polynomial K} (hpa : ∀ t : F, rsFamilyA (algebraMap K F a) u₀ (algebraMap K F l) t = (pa.map (algebraMap K F)).eval t) (hpb : ∀ t : F, rsFamilyB (algebraMap K F b) u₀ (algebraMap K F l) t = (pb.map (algebraMap K F)).eval t) (g : Polynomial K) : ((⟨0, 0, 0, pa, pb⟩ : WeierstrassCurve (Polynomial K)).Ψ₃).eval g ≠ 0 :=
  Glue.Psi3_eval_ne_zero_of_rsFamily_aux ha hb hu₀ hpa hpb g

#print axioms solution

end S_RubinSilverberg_Psi3_eval_ne_zero_of_rsFamily
end P2MW
export P2MW.S_RubinSilverberg_Psi3_eval_ne_zero_of_rsFamily (solution)
