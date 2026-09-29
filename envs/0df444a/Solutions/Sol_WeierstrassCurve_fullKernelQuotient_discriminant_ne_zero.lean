-- Prove2me | solution 1 for WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/60f18439-d3e9-5ef2-9f35-ebb042a67772

import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty"

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero.WeierstrassCurve WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ map Affine.Point.some Affine.Point.some.injEq Affine.Point.zero_def toAffine Affine.Point Affine.Point.some_ne_zero Δ Affine.Y_eq_of_X_eq Affine.Point.zero Affine.Point.neg_some fullKernelQuotient fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet fullKernelQuotient_two oddOrderSummingSet veluGy veluQuotient veluQuotient2 veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow isElliptic_veluQuotient2_of_isElliptic exists_addMonoidHom_coe_eq_veluPointMap2 veluPointMap2 veluPointMap2_some_of_eq veluPointMap2_some_of_ne fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2"
p2m_open "WeierstrassCurve"

private theorem _root_.WeierstrassCurve.some_eq_of_X_eq_of_veluGy_eq_zero {F : Type*} [Field F] (W : WeierstrassCurve F)
    {x₀ y₀ y : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (h : W.toAffine.Nonsingular x₀ y) :
    (Affine.Point.some x₀ y h : W.toAffine.Point) = Affine.Point.some x₀ y₀ h₀ := by
  have hneg : W.toAffine.negY x₀ y₀ = y₀ := by
    simp only [veluGy] at hgy
    simp only [Affine.negY]
    linear_combination hgy
  have hy : y = y₀ := by
    rcases Affine.Y_eq_of_X_eq h.1 h₀.1 rfl with hy | hy
    · exact hy
    · rw [hy, hneg]
  subst hy
  rfl

p2m_export "WeierstrassCurve" "some_eq_of_X_eq_of_veluGy_eq_zero"

private theorem _root_.WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_isElliptic
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0 := by
  intro h0
  have h := W.veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow Q hQ
  rw [h0, zero_mul] at h
  exact pow_ne_zero _ W.isUnit_Δ.ne_zero h.symm

p2m_export "WeierstrassCurve" "veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_isElliptic"

private theorem _root_.WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero_of_odd
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {N : ℕ} (hN : Odd N) (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) :
    (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  obtain ⟨n, rfl⟩ := hN
  rw [W.fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet Q n hQ]
  exact W.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_isElliptic n Q hQ

p2m_export "WeierstrassCurve" "fullKernelQuotient_discriminant_ne_zero_of_odd"

private theorem _root_.WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero_two
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2) :
    (W.fullKernelQuotient Q 2).Δ ≠ 0 := by
  rcases Q with _ | ⟨x, y, h⟩
  · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, addOrderOf_zero] at hQ
    exact absurd hQ (by decide)
  ·
    have h2 : (2 : ℕ) • (Affine.Point.some x y h : W.toAffine.Point) = 0 := by
      rw [← hQ]; exact addOrderOf_nsmul_eq_zero _
    have hneg : -(Affine.Point.some x y h : W.toAffine.Point) = Affine.Point.some x y h := by
      rw [neg_eq_iff_add_eq_zero, ← two_nsmul]; exact h2
    rw [Affine.Point.neg_some] at hneg
    have hy : W.toAffine.negY x y = y := by
      have := (Affine.Point.some.injEq _ _ _ _ _ _).mp hneg
      exact this.2
    have hgy : W.veluGy x y = 0 := by
      simp only [veluGy, Affine.negY] at hy ⊢
      linear_combination hy
    rw [W.fullKernelQuotient_two h hgy]
    exact (isElliptic_veluQuotient2_of_isElliptic h.1 hgy).isUnit.ne_zero

p2m_export "WeierstrassCurve" "fullKernelQuotient_discriminant_ne_zero_two"

private theorem _root_.WeierstrassCurve.addOrderOf_veluPointMap2_eq {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {m : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * (m + 1))
    {x₀ y₀ : F} {h₀ : W.toAffine.Nonsingular x₀ y₀}
    (hT : (m + 1) • Q = Affine.Point.some x₀ y₀ h₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    addOrderOf (veluPointMap2 h2 h₀.1 hgy hΔ Q) = m + 1 := by
  obtain ⟨φ, hφ⟩ := W.exists_addMonoidHom_coe_eq_veluPointMap2 h2 h₀.1 hgy hΔ
  rw [← hφ]
  have hne : ∀ k, 0 < k → k < 2 * (m + 1) → k • Q ≠ 0 := fun k hk1 hk2 =>
    nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; exact hk2)

  have hcoords : ∀ i, i < m → ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      (i + 1) • Q = Affine.Point.some x y h ∧ x ≠ x₀ := by
    intro i hi
    rcases hP : (i + 1) • Q with _ | ⟨x, y, h⟩
    · exact absurd (hP.trans Affine.Point.zero_def.symm) (hne (i + 1) (by omega) (by omega))
    · refine ⟨x, y, h, rfl, fun hx => ?_⟩
      subst hx
      have hPT : (i + 1) • Q = (m + 1) • Q := by
        rw [hP, hT, W.some_eq_of_X_eq_of_veluGy_eq_zero h₀ hgy h]
      have := nsmul_injOn_Iio_addOrderOf (x := Q) (by simp only [Set.mem_Iio]; omega)
        (by simp only [Set.mem_Iio]; omega) hPT
      omega

  have hzero : (m + 1) • φ Q = 0 := by
    rw [← map_nsmul φ (m + 1) Q, hT, hφ, veluPointMap2_some_of_eq h2 h₀.1 hgy hΔ h₀ rfl]
    rfl
  have hfin : IsOfFinAddOrder (φ Q) :=
    φ.isOfFinAddOrder (addOrderOf_pos_iff.mp (by rw [hQ]; omega))
  have hk : 0 < addOrderOf (φ Q) := addOrderOf_pos_iff.mpr hfin
  have hdvd : addOrderOf (φ Q) ∣ m + 1 := addOrderOf_dvd_of_nsmul_eq_zero hzero
  have hle : addOrderOf (φ Q) ≤ m + 1 := Nat.le_of_dvd (by omega) hdvd

  have hgt : m < addOrderOf (φ Q) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x, y, h, hP, hx⟩ := hcoords (addOrderOf (φ Q) - 1) (by omega)
    have h0 : (addOrderOf (φ Q) - 1 + 1) • φ Q = 0 := by
      rw [Nat.sub_add_cancel hk, addOrderOf_nsmul_eq_zero]
    rw [← map_nsmul φ (addOrderOf (φ Q) - 1 + 1) Q, hP, hφ,
      veluPointMap2_some_of_ne h2 h₀.1 hgy hΔ h hx] at h0
    exact Affine.Point.some_ne_zero _ h0
  omega

p2m_export "WeierstrassCurve" "addOrderOf_veluPointMap2_eq"

private theorem discriminant_fullKernelQuotient_ne_zero
    {F : Type*} [Field F] [DecidableEq F] :
    ∀ (N : ℕ) (W : WeierstrassCurve F) [W.IsElliptic], (N : F) ≠ 0 →
      ∀ (Q : W.toAffine.Point), addOrderOf Q = N → (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro W _ hN Q hQ
  rcases Nat.even_or_odd N with ⟨d, rfl⟩ | hodd
  ·
    have hd0 : d ≠ 0 := by rintro rfl; exact hN (by simp)
    obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    have h2 : (2 : F) ≠ 0 := by
      intro h; apply hN; rw [show ((m + 1 + (m + 1) : ℕ) : F) = 2 * (m + 1 : ℕ) by push_cast; ring, h,
        zero_mul]
    have hm1 : ((m + 1 : ℕ) : F) ≠ 0 := by
      intro h; apply hN; rw [show ((m + 1 + (m + 1) : ℕ) : F) = 2 * (m + 1 : ℕ) by push_cast; ring, h,
        mul_zero]
    have hQ' : addOrderOf Q = 2 * (m + 1) := by rw [hQ]; ring

    have hTne : (m + 1) • Q ≠ 0 :=
      nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ']; omega)
    have hT2 : 2 • ((m + 1) • Q) = 0 := by
      rw [← mul_nsmul', ← hQ', addOrderOf_nsmul_eq_zero]
    rcases hT : (m + 1) • Q with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd (hT.trans Affine.Point.zero_def.symm) hTne
    rw [hT] at hT2 hTne
    have hneg : -(Affine.Point.some x₀ y₀ h₀ : W.toAffine.Point) = Affine.Point.some x₀ y₀ h₀ := by
      rw [neg_eq_iff_add_eq_zero, ← two_nsmul]; exact hT2
    rw [Affine.Point.neg_some] at hneg
    have hy : W.toAffine.negY x₀ y₀ = y₀ := ((Affine.Point.some.injEq _ _ _ _ _ _).mp hneg).2
    have hgy : W.veluGy x₀ y₀ = 0 := by
      simp only [veluGy, Affine.negY] at hy ⊢
      linear_combination hy

    have hΔ₁ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := by
      have hord : addOrderOf (Affine.Point.some x₀ y₀ h₀ : W.toAffine.Point) = 2 :=
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        addOrderOf_eq_prime hT2 hTne
      have := W.fullKernelQuotient_discriminant_ne_zero_two _ hord
      rwa [W.fullKernelQuotient_two h₀ hgy] at this
    haveI : (W.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ₁⟩

    rw [show m + 1 + (m + 1) = 2 * (m + 1) by ring,
      W.fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2 h2 Q hQ' hT hgy hΔ₁]
    exact ih (m + 1) (by omega) (W.veluQuotient2 x₀ y₀) hm1 _
      (W.addOrderOf_veluPointMap2_eq h2 Q hQ' hT hgy hΔ₁)
  · exact W.fullKernelQuotient_discriminant_ne_zero_of_odd hodd Q hQ

end WeierstrassCurve

theorem solution
    {F : Type*} [Field F] [DecidableEq F] :
    ∀ (N : ℕ) (W : WeierstrassCurve F) [W.IsElliptic], (N : F) ≠ 0 →
      ∀ (Q : W.toAffine.Point), addOrderOf Q = N → (W.fullKernelQuotient Q N).Δ ≠ 0 :=
  WeierstrassCurve.discriminant_fullKernelQuotient_ne_zero

end S_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero (solution)
