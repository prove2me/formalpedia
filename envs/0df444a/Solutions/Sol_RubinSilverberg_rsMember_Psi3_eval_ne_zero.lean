-- Prove2me | solution 1 for RubinSilverberg.rsMember_Psi3_eval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f5538ef0-4f51-5eae-8e00-81c27c9fa9f7

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Theorems.Thm_RubinSilverberg_kleinCurve_Psi3_eval_ne_zero
import Theorems.Thm_RatFunc_exists_algEquiv_apply_X_eq_moebius
import Theorems.Thm_RubinSilverberg_rsBeta_sub_mul_rsGamma
import Theorems.Thm_RubinSilverberg_IsKleinDatum_kleinH_ne_zero
import Theorems.Thm_RubinSilverberg_IsKleinDatum_kleinT_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_rsMember_Psi3_eval_ne_zero

open Polynomial RubinSilverberg

namespace Pullback
p2m_open "Pullback"

theorem genirr_row {K : Type*} [Field K] [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) (x : RatFunc K) :
    ((kleinCurve (RatFunc.X : RatFunc K)).Ψ₃).eval x ≠ 0 := kleinCurve_Psi3_eval_ne_zero ζ hζ x
theorem moeb_row {K : Type*} [Field K] (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    ∃ φ : RatFunc K ≃ₐ[K] RatFunc K,
      φ RatFunc.X = (RatFunc.C a * RatFunc.X + RatFunc.C b) / (RatFunc.C c * RatFunc.X + RatFunc.C d) :=
  RatFunc.exists_algEquiv_apply_X_eq_moebius a b c d hdet
theorem syz_row {R : Type*} [CommRing R] (u : R) : kleinT u ^ 2 - kleinH u ^ 3 = 1728 * kleinV u ^ 5 := by
  unfold kleinT kleinH kleinV; ring
theorem datumdet_row {K : Type*} [Field K] (u : K) (hu : u ≠ 0) (hf : u ^ 10 + 11 * u ^ 5 - 1 ≠ 0) :
    rsBeta u - u * rsGamma u = -(kleinT u * kleinH u) / (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4) :=
  rsBeta_sub_mul_rsGamma u hu hf
theorem kleinH_ne_row {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (h : IsKleinDatum a b u₀) (ha : a ≠ 0) :
    kleinH u₀ ≠ 0 := h.kleinH_ne_zero ha
theorem kleinT_ne_row {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (h : IsKleinDatum a b u₀) (hb : b ≠ 0) :
    kleinT u₀ ≠ 0 := h.kleinT_ne_zero hb
theorem kleinHHom_smul_row {R : Type*} [CommRing R] (c n d : R) : kleinHHom (c * n) (c * d) = c ^ 20 * kleinHHom n d := by
  unfold kleinHHom; ring
theorem kleinTHom_smul_row {R : Type*} [CommRing R] (c n d : R) : kleinTHom (c * n) (c * d) = c ^ 30 * kleinTHom n d := by
  unfold kleinTHom; ring
theorem kleinHHom_one_right_row {R : Type*} [CommRing R] (n : R) : kleinHHom n 1 = kleinH n := by
  unfold kleinHHom kleinH; ring
theorem kleinTHom_one_right_row {R : Type*} [CommRing R] (n : R) : kleinTHom n 1 = kleinT n := by
  unfold kleinTHom kleinT; ring

section maps
variable {R S : Type*} [CommRing R] [CommRing S] {Φ : Type*} [FunLike Φ R S] [RingHomClass Φ R S]

theorem map_kleinH (f : Φ) (u : R) : f (kleinH u) = kleinH (f u) := by
  simp [kleinH, map_sub, map_add, map_mul, map_pow, map_ofNat]
theorem map_kleinT (f : Φ) (u : R) : f (kleinT u) = kleinT (f u) := by
  simp [kleinT, map_sub, map_add, map_mul, map_pow, map_ofNat]
end maps

section fieldmaps
variable {K L : Type*} [Field K] [Field L] (f : K →+* L)

theorem map_rsBeta (u : K) : f (rsBeta u) = rsBeta (f u) := by
  simp [rsBeta, map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat, map_kleinT]
theorem map_rsGamma (u : K) : f (rsGamma u) = rsGamma (f u) := by
  simp [rsGamma, map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat, map_kleinT]

theorem psi3_short_eval (A B x : K) :
    ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).Ψ₃).eval x = 3 * x ^ 4 + 6 * A * x ^ 2 + 12 * B * x - A ^ 2 := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]
  ring

end fieldmaps

section main
variable {K : Type*} [Field K] [CharZero K]

local notation "FF" => RatFunc K

theorem kleinCurve_map (φ : FF ≃ₐ[K] FF) (u : FF) : (kleinCurve u).map φ.toRingEquiv.toRingHom = kleinCurve (φ u) := by
  simp only [kleinCurve, WeierstrassCurve.map]
  ext <;> simp [map_div₀, map_neg, map_kleinH, map_kleinT, map_ofNat]

theorem psi3_kleinCurve_transport (φ : FF ≃ₐ[K] FF) (y : FF) :
    ((kleinCurve (φ RatFunc.X)).Ψ₃).eval y = φ (((kleinCurve (RatFunc.X : FF)).Ψ₃).eval (φ.symm y)) := by
  rw [← kleinCurve_map, WeierstrassCurve.map_Ψ₃, eval_map]
  conv_lhs => rw [show y = φ.toRingEquiv.toRingHom (φ.symm y) by simp]
  rw [eval₂_at_apply]
  rfl

theorem rsMember_Psi3_eval_ne_zero (ζ : K) (hζ : IsPrimitiveRoot ζ 5) {a b u₀ : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hu₀ : IsKleinDatum a b u₀) (l : K) (x : RatFunc K) :
    ((rsMember (RatFunc.C a) (RatFunc.C b) (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : RatFunc K)).Ψ₃).eval x ≠ 0 := by

  have hH0 : kleinH u₀ ≠ 0 := kleinH_ne_row hu₀ ha
  have hT0 : kleinT u₀ ≠ 0 := kleinT_ne_row hu₀ hb
  have hV : kleinV u₀ ≠ 0 := hu₀.2
  have hu0 : u₀ ≠ 0 := fun h ↦ hV (by rw [kleinV, h, zero_mul])
  have hf : u₀ ^ 10 + 11 * u₀ ^ 5 - 1 ≠ 0 := fun h ↦ hV (by rw [kleinV, h, mul_zero])
  have hrel : 27 * b ^ 2 * kleinH u₀ ^ 3 + 4 * a ^ 3 * kleinT u₀ ^ 2 = 0 := by
    have h1 := hu₀.1
    have h2 := syz_row u₀
    linear_combination h1 + 4 * a ^ 3 * h2
  have hdet : (rsBeta u₀ + l * u₀) * 1 - u₀ * (rsGamma u₀ + l) ≠ 0 := by
    have e : (rsBeta u₀ + l * u₀) * 1 - u₀ * (rsGamma u₀ + l) = rsBeta u₀ - u₀ * rsGamma u₀ := by ring
    rw [e, datumdet_row u₀ hu0 hf]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hT0 hH0))
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hu0)) (pow_ne_zero 4 hf))

  obtain ⟨φ, hφ⟩ := moeb_row (rsBeta u₀ + l * u₀) u₀ (rsGamma u₀ + l) 1 hdet
  set D : FF := RatFunc.C (rsGamma u₀ + l) * RatFunc.X + RatFunc.C 1 with hD_def
  set N : FF := RatFunc.C (rsBeta u₀ + l * u₀) * RatFunc.X + RatFunc.C u₀ with hN_def
  have hD : D ≠ 0 := by
    intro h0
    have : (RatFunc.C (rsGamma u₀ + l) * RatFunc.X + RatFunc.C 1 : FF) =
        algebraMap K[X] FF (Polynomial.C (rsGamma u₀ + l) * Polynomial.X + Polynomial.C 1) := by
      simp [map_add, map_mul]
    rw [hD_def, this, map_eq_zero_iff _ (IsFractionRing.injective K[X] FF)] at h0
    have := congrArg (fun p : K[X] ↦ p.coeff 0) h0
    simp at this
  have hm : φ RatFunc.X = N / D := hφ

  have hN : rsNum (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : FF) = N := by
    simp only [rsNum, hN_def, ← map_rsBeta, map_add, map_mul]
  have hDD : rsDen (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : FF) = D := by
    simp only [rsDen, hD_def, ← map_rsGamma, map_add, map_one]
  have hHH : kleinHHom N D = D ^ 20 * kleinH (φ RatFunc.X) := by
    rw [hm, ← kleinHHom_one_right_row, ← kleinHHom_smul_row, mul_div_cancel₀ _ hD, mul_one]
  have hTT : kleinTHom N D = D ^ 30 * kleinT (φ RatFunc.X) := by
    rw [hm, ← kleinTHom_one_right_row, ← kleinTHom_smul_row, mul_div_cancel₀ _ hD, mul_one]

  set ν : FF := RatFunc.C (-18 * b / a * kleinH u₀ / kleinT u₀) * D ^ 10 with hν_def
  have hC0 : ∀ c : K, (RatFunc.C c : FF) ≠ 0 ↔ c ≠ 0 := fun c ↦ _root_.map_ne_zero RatFunc.C
  have hν0 : ν ≠ 0 := mul_ne_zero ((hC0 _).mpr (by
      refine div_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) hb) ha) hH0) hT0)) (pow_ne_zero 10 hD)
  have hν2 : ν ^ 2 = RatFunc.C (-48 * a / kleinH u₀) * D ^ 20 := by
    rw [hν_def, mul_pow, ← pow_mul, ← map_pow]
    congr 1
    congr 1
    field_simp
    linear_combination 12 * hrel
  have hν3 : ν ^ 3 = RatFunc.C (864 * b / kleinT u₀) * D ^ 30 := by
    rw [pow_succ, hν2, hν_def]
    rw [mul_mul_mul_comm, ← map_mul, ← pow_add]
    congr 1
    congr 1
    field_simp
    norm_num
  have hA : rsFamilyA (RatFunc.C a) (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : FF) =
      ν ^ 2 * (-kleinH (φ RatFunc.X) / 48) := by
    rw [rsFamilyA, hN, hDD, hHH, hν2, ← map_kleinH RatFunc.C u₀]
    have : (RatFunc.C (kleinH u₀) : FF) ≠ 0 := (hC0 _).mpr hH0
    rw [map_div₀, map_mul, map_neg, map_ofNat]
    field_simp
  have hB : rsFamilyB (RatFunc.C b) (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : FF) =
      ν ^ 3 * (kleinT (φ RatFunc.X) / 864) := by
    rw [rsFamilyB, hN, hDD, hTT, hν3, ← map_kleinT RatFunc.C u₀]
    have : (RatFunc.C (kleinT u₀) : FF) ≠ 0 := (hC0 _).mpr hT0
    rw [map_div₀, map_mul, map_ofNat]
    field_simp

  have hscale : ((rsMember (RatFunc.C a) (RatFunc.C b) (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : FF)).Ψ₃).eval x
      = ν ^ 4 * ((kleinCurve (φ RatFunc.X)).Ψ₃).eval (x / ν) := by
    rw [rsMember, hA, hB, kleinCurve, psi3_short_eval, psi3_short_eval]
    field_simp
  rw [hscale, psi3_kleinCurve_transport]
  exact mul_ne_zero (pow_ne_zero 4 hν0)
    ((_root_.map_ne_zero φ).mpr (genirr_row ζ hζ (φ.symm (x / ν))))

end main

end Pullback

open RubinSilverberg in

theorem solution {K : Type*} [Field K] [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) {a b u₀ : K} (ha : a ≠ 0) (hb : b ≠ 0) (hu₀ : IsKleinDatum a b u₀) (l : K) (x : RatFunc K) : ((rsMember (RatFunc.C a) (RatFunc.C b) (RatFunc.C u₀) (RatFunc.C l) (RatFunc.X : RatFunc K)).Ψ₃).eval x ≠ 0 :=
  Pullback.rsMember_Psi3_eval_ne_zero ζ hζ ha hb hu₀ l x

#print axioms solution

end S_RubinSilverberg_rsMember_Psi3_eval_ne_zero
end P2MW
export P2MW.S_RubinSilverberg_rsMember_Psi3_eval_ne_zero (solution)
