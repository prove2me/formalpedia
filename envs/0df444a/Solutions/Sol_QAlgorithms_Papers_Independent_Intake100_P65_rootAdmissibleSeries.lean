-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P65.rootAdmissibleSeries
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-21T15:06:18.9178+00:00
-- url     : https://prove2.me/submissions/78336567-782d-4083-bb56-797f0f961d8f

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

theorem AuxRAS_half (r : ℕ) (q : MvPolynomial (Fin r) ℤ) : integerHalf (2 * q) = q := by
  ext m
  have : MvPolynomial.coeff m (integerHalf (2 * q)) = (MvPolynomial.coeff m (2 * q)) / 2 := rfl
  rw [this, show (2 : MvPolynomial (Fin r) ℤ) = MvPolynomial.C 2 from rfl, MvPolynomial.coeff_C_mul]
  omega

theorem AuxRAS_factor (r : ℕ) (i : Fin r) :
    ∃ G : PowerSeries (MvPolynomial (Fin r) ℤ), schurFactor r i = 1 + 2 * G := by
  refine ⟨PowerSeries.mk fun a => if a = 0 then 0 else MvPolynomial.X i ^ a, ?_⟩
  ext n
  rw [show (2 : PowerSeries (MvPolynomial (Fin r) ℤ)) = PowerSeries.C 2 from rfl]
  rcases n with _ | n <;> simp [schurFactor, PowerSeries.coeff_one]

theorem AuxRAS_prod (r : ℕ) (s : Finset (Fin r)) :
    ∃ H : PowerSeries (MvPolynomial (Fin r) ℤ), ∏ i ∈ s, schurFactor r i = 1 + 2 * H := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j s hj ih =>
    obtain ⟨H, hH⟩ := ih
    obtain ⟨G, hG⟩ := AuxRAS_factor r j
    refine ⟨G + H + 2 * G * H, ?_⟩
    rw [Finset.prod_insert hj, hH, hG]; ring

theorem AuxRAS_even (r a : ℕ) (ha : a ≠ 0) : ∃ h, schurQ r a = 2 * h := by
  obtain ⟨H, hH⟩ := AuxRAS_prod r Finset.univ
  refine ⟨PowerSeries.coeff a H, ?_⟩
  rw [schurQ, hH, map_add, PowerSeries.coeff_one, if_neg ha, zero_add,
    show (2 : PowerSeries (MvPolynomial (Fin r) ℤ)) = PowerSeries.C 2 from rfl,
    PowerSeries.coeff_C_mul]

theorem AuxRAS_zero (r : ℕ) : schurQ r 0 = 1 := by
  rw [schurQ, PowerSeries.coeff_zero_eq_constantCoeff, map_prod]
  apply Finset.prod_eq_one
  intro i _
  simp [schurFactor]

theorem AuxRAS_argeven (r a : ℕ) : ∃ q, (2 * schurQ r (a+1) +
    MvPolynomial.C ((-1 : ℤ) ^ (r-1)) * schurQ r a +
    (if a = 0 then 1 else 0)) = 2 * q := by
  obtain ⟨h1, h1e⟩ := AuxRAS_even r (a+1) (by omega)
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hodd : Odd ((-1 : ℤ) ^ (r-1)) := Odd.pow (by decide)
    obtain ⟨t, ht⟩ := hodd.add_one
    refine ⟨schurQ r 1 + MvPolynomial.C t, ?_⟩
    rw [AuxRAS_zero, if_pos rfl, mul_one, show (0:ℕ)+1 = 1 from rfl,
      show (2 : MvPolynomial (Fin r) ℤ) = MvPolynomial.C 2 from rfl, ← map_one MvPolynomial.C,
      add_assoc, ← map_add, ht, ← two_mul, map_mul]; ring
  · obtain ⟨h0, h0e⟩ := AuxRAS_even r a (by omega)
    refine ⟨schurQ r (a+1) + MvPolynomial.C ((-1) ^ (r-1)) * h0, ?_⟩
    rw [if_neg (by omega : a ≠ 0), h0e]; ring

theorem AuxRAS_omega {R : Type*} [CommRing R] [Invertible (2 : R)] (r a : ℕ) (roots : Fin r → R) :
    evalIntegral roots (universalOmega r a) =
      ⅟ (2 : R) * (2 * evalIntegral roots (schurQ r (a+1)) +
        (-1 : R)^(r-1) * evalIntegral roots (schurQ r a) + (if a = 0 then 1 else 0)) := by
  obtain ⟨q, hq⟩ := AuxRAS_argeven r a
  have e : universalOmega r a = q := by
    rw [universalOmega, etaIntegral]
    simp only [↓reduceIte, one_mul]
    rw [hq, AuxRAS_half]
  have h2 : (MvPolynomial.eval₂Hom (Int.castRingHom R) roots) 2 = 2 := map_ofNat _ 2
  simp only [evalIntegral]
  rw [e, show MvPolynomial.eval₂Hom (Int.castRingHom R) roots q =
    ⅟ (2 : R) * (2 * MvPolynomial.eval₂Hom (Int.castRingHom R) roots q) by simp [← mul_assoc]]
  congr 1
  have := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) roots) hq
  simp only [map_add, map_mul, MvPolynomial.eval₂Hom_C, h2] at this
  rw [← this]
  split_ifs <;> simp

theorem AuxRAS_fac {R : Type*} [CommRing R] (u : R) :
    PowerSeries.mk (fun a => if a = 0 then (1 : R) else 2 * u^a) *
      (1 - PowerSeries.C u * PowerSeries.X) = 1 + PowerSeries.C u * PowerSeries.X := by
  set F := PowerSeries.mk (fun a => if a = 0 then (1 : R) else 2 * u^a) with hF
  rw [mul_sub, mul_one, show F * (PowerSeries.C u * PowerSeries.X) =
    PowerSeries.C u * (PowerSeries.X * F) by ring]
  ext n
  rcases n with _ | n
  · simp [hF]
  · rw [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X, hF,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    rcases n with _ | n <;> simp [pow_succ] <;> ring

theorem AuxRAS_mapfac {R : Type*} [CommRing R] (r : ℕ) (roots : Fin r → R) (i : Fin r) :
    PowerSeries.map (MvPolynomial.eval₂Hom (Int.castRingHom R) roots) (schurFactor r i) =
      PowerSeries.mk (fun a => if a = 0 then (1 : R) else 2 * roots i ^ a) := by
  ext n
  simp only [schurFactor, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

theorem rootAdmissibleSeries (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (r : ℕ) (hr : 1 ≤ r) (roots : Fin r → R) :
    RootAdmissible omega roots ↔
      (PowerSeries.X * PowerSeries.mk omega + 1 -
        PowerSeries.C (⅟ (2 : R)) * PowerSeries.X) *
          (∏ i : Fin r, (1 - PowerSeries.C (roots i) * PowerSeries.X)) =
      (1 - PowerSeries.C (⅟ (2 : R) * (-1 : R)^r) * PowerSeries.X) *
        (∏ i : Fin r, (1 + PowerSeries.C (roots i) * PowerSeries.X)) := by
  set φ := MvPolynomial.eval₂Hom (Int.castRingHom R) roots with hφ
  set Q := PowerSeries.map φ (∏ i : Fin r, schurFactor r i) with hQdef
  set c : R := ⅟ (2 : R) with hc
  have hc2 : c * 2 = 1 := by rw [hc]; simp
  have hs : (-1 : R)^(r-1) = -(-1 : R)^r := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r-1, by omega⟩
    simp [pow_succ]
  have hQ : Q * ∏ i : Fin r, (1 - PowerSeries.C (roots i) * PowerSeries.X) =
      ∏ i : Fin r, (1 + PowerSeries.C (roots i) * PowerSeries.X) := by
    rw [hQdef, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [AuxRAS_mapfac, AuxRAS_fac]
  have hcQ : ∀ n, PowerSeries.coeff n Q = evalIntegral roots (schurQ r n) := by
    intro n; rw [hQdef, PowerSeries.coeff_map]; rfl
  have hunit : IsUnit (∏ i : Fin r, (1 - PowerSeries.C (roots i) * PowerSeries.X)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_prod]
    simp
  rw [← hQ, ← mul_assoc, hunit.mul_left_inj]
  have hL : ∀ n, PowerSeries.coeff (n+1) (PowerSeries.X * PowerSeries.mk omega + 1 -
      PowerSeries.C c * PowerSeries.X) = omega n - (if n = 0 then c else 0) := by
    intro n
    rw [map_sub, map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
    split_ifs <;> simp_all
  have hM : ∀ n, PowerSeries.coeff (n+1) ((1 - PowerSeries.C (c * (-1 : R)^r) * PowerSeries.X) * Q)
      = evalIntegral roots (schurQ r (n+1)) - c * (-1 : R)^r * evalIntegral roots (schurQ r n) := by
    intro n
    rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      hcQ, hcQ]
  have h0 : PowerSeries.coeff 0 (PowerSeries.X * PowerSeries.mk omega + 1 -
      PowerSeries.C c * PowerSeries.X) = PowerSeries.coeff 0
        ((1 - PowerSeries.C (c * (-1 : R)^r) * PowerSeries.X) * Q) := by
    have hq0 : PowerSeries.constantCoeff Q = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcQ, AuxRAS_zero]; simp [evalIntegral]
    simp [hq0]
  unfold RootAdmissible
  simp_rw [AuxRAS_omega]
  constructor
  · intro h
    ext n
    rcases n with _ | n
    · exact h0
    rw [hL, hM, h n]
    split_ifs
    · linear_combination evalIntegral roots (schurQ r (n+1)) * hc2 +
        c * evalIntegral roots (schurQ r n) * hs
    · linear_combination evalIntegral roots (schurQ r (n+1)) * hc2 +
        c * evalIntegral roots (schurQ r n) * hs
  · intro h a
    have := congrArg (PowerSeries.coeff (a+1)) h
    rw [hL, hM] at this
    split_ifs at this ⊢
    · linear_combination this - evalIntegral roots (schurQ r (a+1)) * hc2 -
        c * evalIntegral roots (schurQ r a) * hs
    · linear_combination this - evalIntegral roots (schurQ r (a+1)) * hc2 -
        c * evalIntegral roots (schurQ r a) * hs

end QAlgorithms.Papers.Independent.Intake100.P65

end

theorem solution (R : Type*) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (r : ℕ) (hr : 1 ≤ r) (roots : Fin r → R) :
    QAlgorithms.Papers.Independent.Support21.P12.RootAdmissible omega roots ↔
      (PowerSeries.X * PowerSeries.mk omega + 1 -
        PowerSeries.C (⅟ (2 : R)) * PowerSeries.X) *
          (∏ i : Fin r, (1 - PowerSeries.C (roots i) * PowerSeries.X)) =
      (1 - PowerSeries.C (⅟ (2 : R) * (-1 : R)^r) * PowerSeries.X) *
        (∏ i : Fin r, (1 + PowerSeries.C (roots i) * PowerSeries.X)) :=
  QAlgorithms.Papers.Independent.Intake100.P65.rootAdmissibleSeries R omega r hr roots
