-- Prove2me | solution 1 for RubinSilverberg.exists_variableChange_kleinCurve_eq_rsMember
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4b4417b2-b107-5584-9ca0-34497277bd57

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_exists_variableChange_kleinCurve_eq_rsMember

open RubinSilverberg

namespace S05

theorem syz {R : Type*} [CommRing R] (u : R) : kleinT u ^ 2 - kleinH u ^ 3 = 1728 * kleinV u ^ 5 := by
  unfold kleinT kleinH kleinV; ring
theorem kleinH_div {K : Type*} [Field K] (n : K) {d : K} (hd : d ≠ 0) : kleinH (n / d) = kleinHHom n d / d ^ 20 := by
  unfold kleinH kleinHHom; field_simp
theorem kleinT_div {K : Type*} [Field K] (n : K) {d : K} (hd : d ≠ 0) : kleinT (n / d) = kleinTHom n d / d ^ 30 := by
  unfold kleinT kleinTHom; field_simp
theorem rel {K : Type*} [Field K] {a b u₀ : K} (hd : IsKleinDatum a b u₀) :
    27 * b ^ 2 * kleinH u₀ ^ 3 + 4 * a ^ 3 * kleinT u₀ ^ 2 = 0 := by
  linear_combination hd.1 + 4 * a ^ 3 * syz u₀
theorem kdH {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (hd : IsKleinDatum a b u₀) (ha : a ≠ 0) : kleinH u₀ ≠ 0 := by
  intro hH
  have h1 : (6912 : K) * a ^ 3 * kleinV u₀ ^ 5 = 0 := by
    linear_combination hd.1 - (4 * a ^ 3 + 27 * b ^ 2) * kleinH u₀ ^ 2 * hH
  simp [ha, hd.2] at h1
theorem kdT {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (hd : IsKleinDatum a b u₀) (hb : b ≠ 0) : kleinT u₀ ≠ 0 := by
  intro hT
  have h2 : (46656 : K) * b ^ 2 * kleinV u₀ ^ 5 = 0 := by
    linear_combination -hd.1 + (4 * a ^ 3 + 27 * b ^ 2) * (kleinT u₀ * hT - syz u₀)
  simp [hb, hd.2] at h2

end S05

theorem solution {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (hd : IsKleinDatum a b u₀) (ha : a ≠ 0) (hb : b ≠ 0) (l t k : K) (hden : rsDen u₀ l t ≠ 0) (hk : k ^ 2 = -18 * (b / a) * kleinH u₀ / kleinT u₀) : ∃ C : WeierstrassCurve.VariableChange K, (↑C.u⁻¹ : K) = k * rsDen u₀ l t ^ 5 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ C • kleinCurve (rsNum u₀ l t / rsDen u₀ l t) = rsMember a b u₀ l t := by
  have hH := S05.kdH hd ha
  have hT := S05.kdT hd hb
  have hrel := S05.rel hd
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0] at hk
    have : (-18 : K) * (b / a) * kleinH u₀ / kleinT u₀ = 0 := by rw [← hk]; ring
    simp [ha, hb, hH, hT] at this
  have hne : k * rsDen u₀ l t ^ 5 ≠ 0 := mul_ne_zero hk0 (pow_ne_zero _ hden)
  refine ⟨⟨(Units.mk0 _ hne)⁻¹, 0, 0, 0⟩, ?_, rfl, rfl, rfl, ?_⟩
  · simp
  · have hu : (↑(⟨(Units.mk0 _ hne)⁻¹, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K).u⁻¹ : K)
        = k * rsDen u₀ l t ^ 5 := by simp
    ext
    · simp [WeierstrassCurve.variableChange_a₁, kleinCurve, rsMember]
    · simp [WeierstrassCurve.variableChange_a₂, kleinCurve, rsMember]
    · simp [WeierstrassCurve.variableChange_a₃, kleinCurve, rsMember]
    · rw [WeierstrassCurve.variableChange_a₄, hu]
      simp only [kleinCurve, rsMember, rsFamilyA, mul_zero, sub_zero, add_zero,
        zero_pow two_ne_zero]
      rw [S05.kleinH_div _ hden, show (k * rsDen u₀ l t ^ 5) ^ 4 = (k ^ 2) ^ 2 * rsDen u₀ l t ^ 20 by ring,
        hk]
      field_simp
      linear_combination (-12 * kleinHHom (rsNum u₀ l t) (rsDen u₀ l t)) * hrel
    · rw [WeierstrassCurve.variableChange_a₆, hu]
      simp only [kleinCurve, rsMember, rsFamilyB, mul_zero, zero_mul, sub_zero, add_zero,
        zero_pow two_ne_zero, zero_pow three_ne_zero]
      rw [S05.kleinT_div _ hden, show (k * rsDen u₀ l t ^ 5) ^ 6 = (k ^ 2) ^ 3 * rsDen u₀ l t ^ 30 by ring,
        hk]
      field_simp
      linear_combination (-216 * kleinTHom (rsNum u₀ l t) (rsDen u₀ l t)) * hrel

end S_RubinSilverberg_exists_variableChange_kleinCurve_eq_rsMember
end P2MW
export P2MW.S_RubinSilverberg_exists_variableChange_kleinCurve_eq_rsMember (solution)
