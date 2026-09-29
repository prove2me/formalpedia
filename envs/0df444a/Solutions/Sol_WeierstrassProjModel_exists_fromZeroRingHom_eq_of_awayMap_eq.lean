-- Prove2me | solution 1 for WeierstrassProjModel.exists_fromZeroRingHom_eq_of_awayMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a5ef22fb-8520-5bcd-b148-67f6bf65b439

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_fromZeroRingHom_eq_of_awayMap_eq

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_fromZeroRingHom_eq_of_awayMap_eq.WeierstrassProjModel HomogeneousLocalization HomogeneousIdealQuotientGrading"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal ProjModelRingCR projModelGradingCR"
namespace RingEqualizer
p2m_open "WeierstrassProjModel"

open MvPolynomial

section Monomials

variable {R : Type u} [CommRing R]

theorem X_pow_mul_divMonomial_eq {m n : ℕ} {a b : MvPolynomial (Fin 2) R}
    (h : X 1 ^ m * a = X 0 ^ n * b) :
    X 0 ^ n * (a.divMonomial (Finsupp.single 0 n)) = a := by
  have hmod : a.modMonomial (Finsupp.single 0 n) = 0 := by
    ext d
    rw [MvPolynomial.coeff_zero]
    by_cases hd : Finsupp.single 0 n ≤ d
    · exact coeff_modMonomial_of_le a hd
    · rw [coeff_modMonomial_of_not_le a hd]
      have h1 : coeff (d + Finsupp.single 1 m) (X 1 ^ m * a) = coeff d a := by
        rw [MvPolynomial.X_pow_eq_monomial, coeff_monomial_mul', if_pos le_add_self, one_mul,
          add_tsub_cancel_right]
      have h2 : coeff (d + Finsupp.single 1 m) (X 0 ^ n * b) = 0 := by
        rw [MvPolynomial.X_pow_eq_monomial, coeff_monomial_mul', if_neg]
        intro hle
        apply hd
        intro i
        fin_cases i
        · simpa using hle 0
        · simp
      rw [← h1, h, h2]
  have := a.divMonomial_add_modMonomial (Finsupp.single 0 n)
  rwa [hmod, add_zero, ← MvPolynomial.X_pow_eq_monomial] at this

end Monomials

section Cubic

variable {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)

noncomputable abbrev g : Polynomial (MvPolynomial (Fin 2) R) := (ProjWeierstrassCubicPrime.wCubic V).toPoly

lemma g_monic : (g V).Monic := ProjWeierstrassCubicPrime.wCubic_toPoly_monic V

lemma mk_eq_zero_iff (P : MvPolynomial (Fin 3) R) :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal P = 0 ↔ g V ∣ finSuccEquiv R 2 P := by
  rw [Ideal.Quotient.eq_zero_iff_mem, projModelHomogeneousIdealCR_toIdeal, Ideal.mem_span_singleton,
    ← map_dvd_iff (finSuccEquiv R 2).toMulEquiv]
  show finSuccEquiv R 2 V.polynomial ∣ finSuccEquiv R 2 P ↔ _
  rw [ProjWeierstrassCubicPrime.finSuccEquiv_polynomial]
  exact neg_dvd

private lemma _root_.WeierstrassProjModel.RingEqualizer.mk_eq_mk_iff (P Q : MvPolynomial (Fin 3) R) :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal P =
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal Q ↔
      (finSuccEquiv R 2 P) %ₘ g V = (finSuccEquiv R 2 Q) %ₘ g V := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff, ← Polynomial.modByMonic_eq_zero_iff_dvd (g_monic V),
    map_sub, Polynomial.sub_modByMonic, sub_eq_zero]

p2m_export "WeierstrassProjModel.RingEqualizer" "mk_eq_mk_iff"
lemma finSuccEquiv_X1 : finSuccEquiv R 2 (X 1 : MvPolynomial (Fin 3) R) = Polynomial.C (X 0) :=
  finSuccEquiv_X_succ (j := (0 : Fin 2))

lemma finSuccEquiv_X2 : finSuccEquiv R 2 (X 2 : MvPolynomial (Fin 3) R) = Polynomial.C (X 1) :=
  finSuccEquiv_X_succ (j := (1 : Fin 2))

lemma symm_C_X0 : (finSuccEquiv R 2).symm (Polynomial.C (X 0)) = (X 1 : MvPolynomial (Fin 3) R) := by
  rw [← finSuccEquiv_X1, AlgEquiv.symm_apply_apply]

lemma symm_C_X1 : (finSuccEquiv R 2).symm (Polynomial.C (X 1)) = (X 2 : MvPolynomial (Fin 3) R) := by
  rw [← finSuccEquiv_X2, AlgEquiv.symm_apply_apply]

lemma mk_eq_mk_symm_modByMonic (P : MvPolynomial (Fin 3) R) :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal P =
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        ((finSuccEquiv R 2).symm ((finSuccEquiv R 2 P) %ₘ g V)) := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff, map_sub, AlgEquiv.apply_symm_apply]
  refine ⟨(finSuccEquiv R 2 P) /ₘ g V, ?_⟩
  exact sub_eq_of_eq_add' (Polynomial.modByMonic_add_div (finSuccEquiv R 2 P) (g V)).symm

lemma eq_zero_of_mk_X_succ_mul_eq_zero (j : Fin 2) {a : ProjModelRingCR V}
    (h : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X j.succ) * a = 0) : a = 0 := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [← map_mul, mk_eq_zero_iff, ← Polynomial.modByMonic_eq_zero_iff_dvd (g_monic V), map_mul,
    finSuccEquiv_X_succ, Polynomial.C_mul', Polynomial.smul_modByMonic] at h
  rw [mk_eq_zero_iff, ← Polynomial.modByMonic_eq_zero_iff_dvd (g_monic V)]
  refine Polynomial.ext fun i ↦ ?_
  have hi := congrArg (fun p ↦ Polynomial.coeff p i) h
  simp only [Polynomial.coeff_smul, Polynomial.coeff_zero, smul_eq_mul] at hi
  rw [Polynomial.coeff_zero]
  exact (isRegular_X (R := R) (n := j)).left (hi.trans (mul_zero _).symm)

lemma isRegular_mk_X_succ (j : Fin 2) :
    IsRegular (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X j.succ : MvPolynomial (Fin 3) R)) := by
  have hl : IsLeftRegular
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X j.succ : MvPolynomial (Fin 3) R)) := by
    intro a b hab
    rw [← sub_eq_zero] at hab ⊢
    exact eq_zero_of_mk_X_succ_mul_eq_zero V j (by rwa [mul_sub])
  exact ⟨hl, fun a b hab ↦ hl (by simpa only [mul_comm] using hab)⟩

lemma exists_eq_mul_of_eq {m n : ℕ} (α β : ProjModelRingCR V)
    (h : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 2) ^ m * α =
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 1) ^ n * β) :
    ∃ γ : ProjModelRingCR V,
      α = Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 1) ^ n * γ ∧
      β = Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 2) ^ m * γ := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective α
  obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective β
  set p₀ := (finSuccEquiv R 2 P) %ₘ g V with hp₀
  set q₀ := (finSuccEquiv R 2 Q) %ₘ g V with hq₀

  have key : (X 1 ^ m : MvPolynomial (Fin 2) R) • p₀ = (X 0 ^ n : MvPolynomial (Fin 2) R) • q₀ := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, mk_eq_mk_iff, map_mul, map_mul, map_pow, map_pow,
      finSuccEquiv_X1, finSuccEquiv_X2, ← Polynomial.C_pow, ← Polynomial.C_pow, Polynomial.C_mul',
      Polynomial.C_mul', Polynomial.smul_modByMonic, Polynomial.smul_modByMonic] at h
    exact h

  let c : Polynomial (MvPolynomial (Fin 2) R) :=
    ⟨.ofCoeff (p₀.toFinsupp.coeff.mapRange (fun a ↦ a.divMonomial (Finsupp.single 0 n)) (zero_divMonomial _))⟩
  have hc : ∀ i, c.coeff i = (p₀.coeff i).divMonomial (Finsupp.single 0 n) := fun i ↦ by
    simp only [c, Polynomial.coeff_ofFinsupp, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply]; rfl
  have keyi : ∀ i, X 1 ^ m * p₀.coeff i = X 0 ^ n * q₀.coeff i := fun i ↦ by
    have := congrArg (fun p ↦ Polynomial.coeff p i) key
    simpa only [Polynomial.coeff_smul, smul_eq_mul] using this
  have hp : (X 0 ^ n : MvPolynomial (Fin 2) R) • c = p₀ := by
    refine Polynomial.ext fun i ↦ ?_
    rw [Polynomial.coeff_smul, smul_eq_mul, hc, X_pow_mul_divMonomial_eq (keyi i)]
  have hq : (X 1 ^ m : MvPolynomial (Fin 2) R) • c = q₀ := by
    refine Polynomial.ext fun i ↦ ?_
    rw [Polynomial.coeff_smul, smul_eq_mul, hc]
    apply (isRegular_X_pow (R := R) (n := (0 : Fin 2)) n).left
    show X 0 ^ n * _ = X 0 ^ n * _
    rw [← mul_assoc, mul_comm (X 0 ^ n), mul_assoc, X_pow_mul_divMonomial_eq (keyi i), keyi i]

  refine ⟨Ideal.Quotient.mk _ ((finSuccEquiv R 2).symm c), ?_, ?_⟩
  · rw [mk_eq_mk_symm_modByMonic V P, ← hp₀, ← hp, ← Polynomial.C_mul', Polynomial.C_pow, map_mul, map_pow,
      symm_C_X0, map_mul, map_pow]
  · rw [mk_eq_mk_symm_modByMonic V Q, ← hq₀, ← hq, ← Polynomial.C_mul', Polynomial.C_pow, map_mul, map_pow,
      symm_C_X1, map_mul, map_pow]

lemma exists_mem_zero_eq_mul_of_eq {m n : ℕ} (α β : ProjModelRingCR V)
    (hα : α ∈ projModelGradingCR V n) (hβ : β ∈ projModelGradingCR V m)
    (h : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 2) ^ m * α =
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 1) ^ n * β) :
    ∃ r : projModelGradingCR V 0,
      α = Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 1) ^ n * r ∧
      β = Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 2) ^ m * r := by
  classical
  obtain ⟨γ, hαγ, hβγ⟩ := exists_eq_mul_of_eq V α β h
  have hY : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 1 : MvPolynomial (Fin 3) R) ^ n ∈
      projModelGradingCR V n := by
    simpa only [smul_eq_mul, mul_one] using SetLike.pow_mem_graded n
      (mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R 1)) :
        Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 1 : MvPolynomial (Fin 3) R) ∈
          projModelGradingCR V 1)
  have hZ : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 2 : MvPolynomial (Fin 3) R) ^ m ∈
      projModelGradingCR V m := by
    simpa only [smul_eq_mul, mul_one] using SetLike.pow_mem_graded m
      (mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R 2)) :
        Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X 2 : MvPolynomial (Fin 3) R) ∈
          projModelGradingCR V 1)
  refine ⟨DirectSum.decompose (projModelGradingCR V) γ 0, ?_, ?_⟩
  · calc α = (DirectSum.decompose (projModelGradingCR V) α n : ProjModelRingCR V) :=
          (DirectSum.decompose_of_mem_same _ hα).symm
      _ = _ := by
          rw [hαγ, DirectSum.coe_decompose_mul_of_left_mem_of_le (𝒜 := projModelGradingCR V) hY le_rfl,
            Nat.sub_self]
  · calc β = (DirectSum.decompose (projModelGradingCR V) β m : ProjModelRingCR V) :=
          (DirectSum.decompose_of_mem_same _ hβ).symm
      _ = _ := by
          rw [hβγ, DirectSum.coe_decompose_mul_of_left_mem_of_le (𝒜 := projModelGradingCR V) hZ le_rfl,
            Nat.sub_self]

end Cubic

end WeierstrassProjModel.RingEqualizer

open WeierstrassProjModel.RingEqualizer MvPolynomial in

theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) :
    let 𝒜 := projModelGradingCR V
    let Y : ProjModelRingCR V := Ideal.Quotient.mk _ (MvPolynomial.X 1)
    let Z : ProjModelRingCR V := Ideal.Quotient.mk _ (MvPolynomial.X 2)
    let hY : Y ∈ 𝒜 1 :=
      mk_mem_quotGradingSubmodule _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 1))
    let hZ : Z ∈ 𝒜 1 :=
      mk_mem_quotGradingSubmodule _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 2))
    Function.Injective (fromZeroRingHom 𝒜 (Submonoid.powers Y)) ∧
    ∀ (a : Away 𝒜 Y) (b : Away 𝒜 Z),
      awayMap 𝒜 hZ (rfl : Y * Z = Y * Z) a = awayMap 𝒜 hY (mul_comm Y Z) b →
      ∃ r : 𝒜 0, fromZeroRingHom 𝒜 (Submonoid.powers Y) r = a ∧ fromZeroRingHom 𝒜 (Submonoid.powers Z) r = b := by
  intro 𝒜 Y Z hY hZ
  have hYreg : IsRegular Y := isRegular_mk_X_succ V 0
  have hZreg : IsRegular Z := isRegular_mk_X_succ V 1
  have val_fromZero : ∀ (S : Submonoid (ProjModelRingCR V)) (r : 𝒜 0),
      (fromZeroRingHom 𝒜 S r).val = Localization.mk (r : ProjModelRingCR V) 1 := fun S r ↦ rfl
  refine ⟨fun r₁ r₂ h ↦ ?_, fun a b hab ↦ ?_⟩
  · have hv := congrArg HomogeneousLocalization.val h
    rw [val_fromZero, val_fromZero, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hv
    obtain ⟨⟨c, hc⟩, hv⟩ := hv
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hc
    simp only [OneMemClass.coe_one, one_mul] at hv
    exact Subtype.ext (((hYreg.pow k).left hv).symm).symm
  · obtain ⟨n, α, hα, rfl⟩ := Away.mk_surjective 𝒜 hY a
    obtain ⟨m, β, hβ, rfl⟩ := Away.mk_surjective 𝒜 hZ b
    have hα' : α ∈ 𝒜 n := by simpa using hα
    have hβ' : β ∈ 𝒜 m := by simpa using hβ
    have hv := congrArg HomogeneousLocalization.val hab
    rw [HomogeneousLocalization.Away.mk, HomogeneousLocalization.Away.mk, val_awayMap_mk, val_awayMap_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hv
    obtain ⟨⟨c, hc⟩, hv⟩ := hv
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hc
    simp only at hv

    have key : Z ^ m * α = Y ^ n * β := by
      have e : (Y * Z) ^ k * (Y ^ m * (Z ^ n * (Z ^ m * α))) = (Y * Z) ^ k * (Y ^ m * (Z ^ n * (Y ^ n * β))) := by
        calc _ = (Y * Z) ^ k * ((Y * Z) ^ m * (α * Z ^ n)) := by ring
          _ = (Y * Z) ^ k * ((Y * Z) ^ n * (β * Y ^ m)) := hv
          _ = _ := by ring
      exact (hZreg.pow n).left ((hYreg.pow m).left (((IsRegular.mul hYreg hZreg).pow k).left e))
    obtain ⟨r, hαr, hβr⟩ := exists_mem_zero_eq_mul_of_eq V α β hα' hβ' key
    have hαr' : α = Y ^ n * r := hαr
    have hβr' : β = Z ^ m * r := hβr
    refine ⟨r, ?_, ?_⟩
    · apply HomogeneousLocalization.val_injective
      rw [val_fromZero, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp [hαr']⟩
    · apply HomogeneousLocalization.val_injective
      rw [val_fromZero, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp [hβr']⟩

end S_WeierstrassProjModel_exists_fromZeroRingHom_eq_of_awayMap_eq
end P2MW
export P2MW.S_WeierstrassProjModel_exists_fromZeroRingHom_eq_of_awayMap_eq (solution)
