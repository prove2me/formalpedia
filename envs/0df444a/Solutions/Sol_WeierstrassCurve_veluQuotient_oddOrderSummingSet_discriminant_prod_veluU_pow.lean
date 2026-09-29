-- Prove2me | solution 1 for WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/385e903a-5861-5690-a3fb-0631656baf3f

import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluVariableChange
import Definitions.Def_WeierstrassCurve_VeluEquivariance
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

set_option autoImplicit false
set_option Elab.async false

namespace N5IDAux4

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in

private lemma equation_b (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0) {x y : F}
    (h : W.toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  rw [Affine.equation_iff, ha1, ha3] at h
  linear_combination h

private lemma chord_prod (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0) {x₁ y₁ x₂ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)
      * W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))
      = ((x₁ * x₂ - W.a₄) ^ 2 - 4 * W.a₆ * (x₁ + x₂ + W.a₂)) / (x₁ - x₂) ^ 2 := by
  have e₁ := equation_b W ha1 ha3 h₁
  have e₂ := equation_b W ha1 ha3 h₂
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx]
  simp only [Affine.addX, Affine.negY, toAffine, ha1, ha3]
  field_simp
  linear_combination (norm := ring_nf)
    (y₁ ^ 2 - 2 * y₂ ^ 2 - 2 * x₂ ^ 3 + 2 * x₁ * x₂ ^ 2 + 2 * x₁ ^ 2 * x₂ - x₁ ^ 3 + W.a₆
        + W.a₄ * x₁ - 2 * W.a₂ * x₂ ^ 2 + 4 * W.a₂ * x₁ * x₂ - W.a₂ * x₁ ^ 2) * e₁
      + (y₂ ^ 2 - x₂ ^ 3 + 2 * x₁ * x₂ ^ 2 + 2 * x₁ ^ 2 * x₂ - 4 * x₁ ^ 3 - W.a₆ + W.a₄ * x₂
        - 2 * W.a₄ * x₁ - W.a₂ * x₂ ^ 2 + 4 * W.a₂ * x₁ * x₂ - 4 * W.a₂ * x₁ ^ 2) * e₂

private lemma double_x (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0) {x y : F}
    (hy : y ≠ W.toAffine.negY x y) :
    W.toAffine.addX x x (W.toAffine.slope x x y y)
      = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 / (2 * y) ^ 2 - W.a₂ - 2 * x := by
  have h2y : (2 : F) * y ≠ 0 := by
    intro hc
    apply hy
    simp only [Affine.negY, toAffine, ha1, ha3]
    linear_combination hc
  rw [Affine.slope_of_Y_ne rfl hy]
  simp only [Affine.addX, Affine.negY, toAffine, ha1, ha3]
  field_simp
  ring

private lemma chord_sum' {x₁ y₁ x₂ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)
      + W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))
      = 2 * x₂ + W.veluT x₂ y₂ / (x₁ - x₂) + W.veluU x₂ y₂ / (x₁ - x₂) ^ 2 := by
  have e₁ := (Affine.equation_iff (W := W.toAffine) x₁ y₁).mp h₁
  have e₂ := (Affine.equation_iff (W := W.toAffine) x₂ y₂).mp h₂
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx]
  simp only [Affine.addX, Affine.negY, veluT, veluU, veluGx, veluGy, toAffine]
  field_simp
  linear_combination (norm := ring_nf) 2 * e₁ - 2 * e₂

section Reindex

variable {V : Affine F}

omit [DecidableEq F] in

private lemma coordsOrZero_neg_fst (P : V.Point) :
    (-P).coordsOrZero.1 = P.coordsOrZero.1 := by
  cases P <;> rfl

private lemma sub_smul_eq_neg_smul {Q : V.Point} {N m : ℕ} (hN : addOrderOf Q = N) (hm : m ≤ N) :
    (N - m) • Q = -(m • Q) := by
  have h0 : N • Q = 0 := by rw [← hN]; exact addOrderOf_nsmul_eq_zero Q
  have hadd : (N - m) • Q + m • Q = 0 := by
    rw [← add_nsmul, Nat.sub_add_cancel hm, h0]
  exact eq_neg_of_add_eq_zero_left hadd

private lemma coordsOrZero_sub_smul_fst {Q : V.Point} {N m : ℕ} (hN : addOrderOf Q = N)
    (hm : m ≤ N) :
    ((N - m) • Q).coordsOrZero.1 = (m • Q).coordsOrZero.1 := by
  rw [sub_smul_eq_neg_smul hN hm, coordsOrZero_neg_fst]

private def fold2 (n k : ℕ) : ℕ := if 2 * k ≤ n then 2 * k else 2 * n + 1 - 2 * k

private def unfold2 (n m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else (2 * n + 1 - m) / 2

private lemma fold2_mem {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) : fold2 n k ∈ Finset.Icc 1 n := by
  simp only [Finset.mem_Icc] at *
  unfold fold2
  split <;> omega

private lemma unfold2_fold2 {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) : unfold2 n (fold2 n k) = k := by
  simp only [Finset.mem_Icc] at hk
  unfold fold2 unfold2
  split <;> split <;> omega

private lemma coordsOrZero_fold2_smul_fst {Q : V.Point} {n : ℕ} (hQ : addOrderOf Q = 2 * n + 1)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    ((fold2 n k) • Q).coordsOrZero.1 = ((2 * k) • Q).coordsOrZero.1 := by
  simp only [Finset.mem_Icc] at hk
  unfold fold2
  split
  · rfl
  · exact coordsOrZero_sub_smul_fst hQ (by omega)

end Reindex

section Structure

variable {V : WeierstrassCurve F} {Q : V.toAffine.Point} {n : ℕ}

omit [DecidableEq F] in

private lemma exists_some_of_ne_zero {P : V.toAffine.Point} (hP : P ≠ 0) :
    ∃ (x y : F) (h : V.toAffine.Nonsingular x y), P = Affine.Point.some x y h ∧
      P.coordsOrZero = (x, y) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨x, y, h, rfl, rfl⟩

private lemma nsmul_ne_zero (hQ : addOrderOf Q = 2 * n + 1) {k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k ≤ 2 * n) : k • Q ≠ 0 := by
  intro h
  have hdvd : 2 * n + 1 ∣ k := hQ ▸ (addOrderOf_dvd_iff_nsmul_eq_zero).mpr h
  have := Nat.le_of_dvd (by omega) hdvd
  omega

private lemma two_nsmul_nsmul_ne_zero (hQ : addOrderOf Q = 2 * n + 1) {k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k ≤ n) : (2 : ℕ) • (k • Q) ≠ 0 := by
  intro h
  have h' : (k + k) • Q = 0 := by
    rw [add_nsmul, ← two_nsmul]
    exact h
  exact nsmul_ne_zero hQ (k := k + k) (by omega) (by omega) h'

private lemma nsmul_injOn_Icc (hQ : addOrderOf Q = 2 * n + 1) {k k' : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hk'1 : 1 ≤ k') (hk'n : k' ≤ n) (heq : k • Q = k' • Q) : k = k' := by
  wlog hle : k' ≤ k generalizing k k'
  · exact (this hk'1 hk'n hk1 hkn heq.symm (by omega)).symm
  have hsub : (k - k') • Q = 0 := by
    have h1 : (k - k') • Q + k' • Q = k' • Q := by
      rw [← add_nsmul, Nat.sub_add_cancel hle, heq]
    exact add_right_cancel (h1.trans (zero_add _).symm)
  have hdvd : 2 * n + 1 ∣ k - k' := hQ ▸ (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hsub
  rcases Nat.eq_zero_or_pos (k - k') with h0 | h0
  · omega
  · have := Nat.le_of_dvd h0 hdvd
    omega

private lemma nsmul_eq_of_x_eq (hQ : addOrderOf Q = 2 * n + 1) {k k' : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hk'1 : 1 ≤ k') (hk'n : k' ≤ n)
    {x y : F} {h : V.toAffine.Nonsingular x y} (heq : k • Q = Affine.Point.some x y h)
    {x' y' : F} {h' : V.toAffine.Nonsingular x' y'} (heq' : k' • Q = Affine.Point.some x' y' h')
    (hx : x = x') : k • Q = k' • Q := by
  rcases (Affine.Point.X_eq_iff (h₁ := h) (h₂ := h')).mp hx with hPP | hPP
  · rw [heq, heq', hPP]
  · exfalso
    have hsum : (k + k') • Q = 0 := by
      rw [add_nsmul, heq, heq', hPP, neg_add_cancel]
    have hdvd : 2 * n + 1 ∣ k + k' := hQ ▸ (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hsum
    have := Nat.le_of_dvd (by omega) hdvd
    omega

private lemma exists_nsmul_of_mem (hQ : addOrderOf Q = 2 * n + 1) {P : F × F}
    (hP : P ∈ V.oddOrderSummingSet Q n) :
    ∃ (k : ℕ) (x y : F) (h : V.toAffine.Nonsingular x y), 1 ≤ k ∧ k ≤ n ∧
      k • Q = Affine.Point.some x y h ∧ P = (x, y) ∧ (2 : ℕ) • (k • Q) ≠ 0 := by
  obtain ⟨k, hk1, hkn, hkP⟩ := V.mem_oddOrderSummingSet.mp hP
  have hne : k • Q ≠ 0 := nsmul_ne_zero hQ hk1 (by omega)
  obtain ⟨x, y, h, heq, hcoords⟩ := exists_some_of_ne_zero hne
  refine ⟨k, x, y, h, hk1, hkn, heq, ?_, two_nsmul_nsmul_ne_zero hQ hk1 hkn⟩
  rw [← hkP]
  exact hcoords

private lemma veluGy_ne_zero_of_two_nsmul_ne_zero {x y : F} (h : V.toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • (Affine.Point.some x y h : V.toAffine.Point) ≠ 0) :
    V.veluGy x y ≠ 0 := by
  intro h0
  have hy : y = V.toAffine.negY x y := by
    have hkey : V.toAffine.negY x y = y + V.veluGy x y := by
      simp only [Affine.negY, veluGy]; ring
    rw [hkey, h0, add_zero]
  exact h2 (by rw [two_nsmul]; exact Affine.Point.add_self_of_Y_eq hy)

private theorem isOddVeluSet_oddOrderSummingSet' (hQ : addOrderOf Q = 2 * n + 1) :
    V.IsOddVeluSet (V.oddOrderSummingSet Q n) where
  equation P hP := by
    obtain ⟨k, x, y, h, _, _, _, hPxy, _⟩ := exists_nsmul_of_mem hQ hP
    rw [hPxy]
    exact h.left
  gy_ne_zero P hP := by
    obtain ⟨k, x, y, h, _, _, heq, hPxy, h2k⟩ := exists_nsmul_of_mem hQ hP
    rw [hPxy]
    exact veluGy_ne_zero_of_two_nsmul_ne_zero h (heq ▸ h2k)
  x_injOn P hP P' hP' hx := by
    obtain ⟨k, x, y, h, hk1, hkn, heq, hPxy, _⟩ := exists_nsmul_of_mem hQ hP
    obtain ⟨k', x', y', h', hk'1, hk'n, heq', hP'xy, _⟩ := exists_nsmul_of_mem hQ hP'
    subst hPxy; subst hP'xy
    have hQQ' : k • Q = k' • Q :=
      nsmul_eq_of_x_eq hQ hk1 hkn hk'1 hk'n heq heq' hx
    have hpt : (Affine.Point.some x y h : V.toAffine.Point) = Affine.Point.some x' y' h' := by
      rw [← heq, ← heq']; exact hQQ'
    have hcp := congrArg Affine.Point.coordsOrZero hpt
    simpa using hcp

private lemma coordsOrZero_nsmul_injOn (hQ : addOrderOf Q = 2 * n + 1) :
    Set.InjOn (fun k : ℕ => (k • Q).coordsOrZero) (Finset.Icc 1 n : Finset ℕ) := by
  intro k hk k' hk' hcoords
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
  obtain ⟨x, y, h, heq, hc⟩ :=
    exists_some_of_ne_zero (nsmul_ne_zero hQ hk.1 (by omega))
  obtain ⟨x', y', h', heq', hc'⟩ :=
    exists_some_of_ne_zero (nsmul_ne_zero hQ hk'.1 (by omega))
  have hcc : ((x, y) : F × F) = (x', y') := by
    rw [← hc, ← hc']; exact hcoords
  exact nsmul_injOn_Icc hQ hk.1 hk.2 hk'.1 hk'.2
    (nsmul_eq_of_x_eq hQ hk.1 hk.2 hk'.1 hk'.2 heq heq' (congrArg Prod.fst hcc))

private theorem card_oddOrderSummingSet' (hQ : addOrderOf Q = 2 * n + 1) :
    (V.oddOrderSummingSet Q n).card = n := by
  rw [oddOrderSummingSet, Finset.card_image_of_injOn (coordsOrZero_nsmul_injOn hQ),
    Nat.card_Icc, Nat.add_sub_cancel]

private lemma sum_oddOrderSummingSet_eq (hQ : addOrderOf Q = 2 * n + 1)
    {M : Type*} [AddCommMonoid M] (g : F × F → M) :
    ∑ P ∈ V.oddOrderSummingSet Q n, g P
      = ∑ k ∈ Finset.Icc 1 n, g ((k • Q).coordsOrZero) := by
  rw [oddOrderSummingSet, Finset.sum_image (fun k hk k' hk' h =>
    coordsOrZero_nsmul_injOn hQ (by simpa using hk) (by simpa using hk') h)]

private lemma prod_oddOrderSummingSet_eq (hQ : addOrderOf Q = 2 * n + 1)
    {M : Type*} [CommMonoid M] (g : F × F → M) :
    ∏ P ∈ V.oddOrderSummingSet Q n, g P
      = ∏ k ∈ Finset.Icc 1 n, g ((k • Q).coordsOrZero) := by
  rw [oddOrderSummingSet, Finset.prod_image (fun k hk k' hk' h =>
    coordsOrZero_nsmul_injOn hQ (by simpa using hk) (by simpa using hk') h)]

end Structure

section Translation

variable {V : WeierstrassCurve F}

private lemma addX_two_torsion_sub_root (ha1 : V.a₁ = 0) (ha3 : V.a₃ = 0) {e₁ e₂ e₃ xT yT : F}
    (hσ1 : e₁ + e₂ + e₃ = -V.a₂) (hσ2 : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = V.a₄)
    (hσ3 : e₁ * e₂ * e₃ = -V.a₆) (hT : V.toAffine.Equation xT yT) (h1 : xT ≠ e₁) :
    V.toAffine.addX e₁ xT (V.toAffine.slope e₁ xT 0 yT) - e₂
      = (e₁ - e₂) * (xT - e₃) / (xT - e₁) := by
  have eT := equation_b V ha1 ha3 hT
  have hd : xT - e₁ ≠ 0 := sub_ne_zero.mpr h1
  have hd' : e₁ - xT ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [Affine.slope_of_X_ne (fun h => h1 h.symm)]
  simp only [Affine.addX, toAffine, ha1]
  field_simp
  linear_combination (norm := ring_nf) (xT - e₁) * eT
    + (2 * e₁ * xT ^ 2 - 3 * e₁ ^ 2 * xT + e₁ ^ 3) * hσ1
    + (e₁ * xT - xT ^ 2) * hσ2 + (xT - e₁) * hσ3

private lemma addX_two_torsion_sub_self (ha1 : V.a₁ = 0) (ha3 : V.a₃ = 0) {e₁ e₂ e₃ xT yT : F}
    (hσ1 : e₁ + e₂ + e₃ = -V.a₂) (hσ2 : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = V.a₄)
    (hσ3 : e₁ * e₂ * e₃ = -V.a₆) (hT : V.toAffine.Equation xT yT) (h1 : xT ≠ e₁) :
    V.toAffine.addX e₁ xT (V.toAffine.slope e₁ xT 0 yT) - e₁
      = (e₁ - e₂) * (e₁ - e₃) / (xT - e₁) := by
  have eT := equation_b V ha1 ha3 hT
  have hd : xT - e₁ ≠ 0 := sub_ne_zero.mpr h1
  have hd' : e₁ - xT ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [Affine.slope_of_X_ne (fun h => h1 h.symm)]
  simp only [Affine.addX, toAffine, ha1]
  field_simp
  linear_combination (norm := ring_nf) (xT - e₁) * eT
    + (2 * e₁ * xT ^ 2 - 3 * e₁ ^ 2 * xT + e₁ ^ 3) * hσ1
    + (e₁ * xT - xT ^ 2) * hσ2 + (xT - e₁) * hσ3

end Translation

section Pack

variable {V : WeierstrassCurve F}

omit [DecidableEq F] in
private lemma two_mul_y_ne_zero (ha1 : V.a₁ = 0) (ha3 : V.a₃ = 0) {x y : F}
    (hy : y ≠ V.toAffine.negY x y) : (2 : F) * y ≠ 0 := by
  intro hc
  apply hy
  simp only [Affine.negY, toAffine, ha1, ha3]
  linear_combination hc

private lemma double_x_mul_psi2Sq (ha1 : V.a₁ = 0) (ha3 : V.a₃ = 0) {x y : F}
    (h : V.toAffine.Equation x y) (hy : y ≠ V.toAffine.negY x y) :
    V.toAffine.addX x x (V.toAffine.slope x x y y)
        * (4 * x ^ 3 + V.b₂ * x ^ 2 + 2 * V.b₄ * x + V.b₆)
      = x ^ 4 - V.b₄ * x ^ 2 - 2 * V.b₆ * x - V.b₈ := by
  have e := equation_b V ha1 ha3 h
  have h2y : (2 : F) * y ≠ 0 := two_mul_y_ne_zero ha1 ha3 hy
  have h4 : ((2 : F) * y) ^ 2 ≠ 0 := pow_ne_zero 2 h2y
  have hclear : V.toAffine.addX x x (V.toAffine.slope x x y y) * ((2 : F) * y) ^ 2
      = (3 * x ^ 2 + 2 * V.a₂ * x + V.a₄) ^ 2 - (V.a₂ + 2 * x) * ((2 : F) * y) ^ 2 := by
    have hy0 : y ≠ 0 := fun h0 => h2y (by rw [h0, mul_zero])
    have h2ne : (2 : F) ≠ 0 := fun hc => h2y (by rw [hc, zero_mul])
    rw [double_x V ha1 ha3 hy]
    field_simp
    ring
  apply mul_right_cancel₀ h4
  calc (V.toAffine.addX x x (V.toAffine.slope x x y y)
          * (4 * x ^ 3 + V.b₂ * x ^ 2 + 2 * V.b₄ * x + V.b₆)) * ((2 : F) * y) ^ 2
      = (V.toAffine.addX x x (V.toAffine.slope x x y y) * ((2 : F) * y) ^ 2)
          * (4 * x ^ 3 + V.b₂ * x ^ 2 + 2 * V.b₄ * x + V.b₆) := by ring
    _ = ((3 * x ^ 2 + 2 * V.a₂ * x + V.a₄) ^ 2 - (V.a₂ + 2 * x) * ((2 : F) * y) ^ 2)
          * (4 * x ^ 3 + V.b₂ * x ^ 2 + 2 * V.b₄ * x + V.b₆) := by rw [hclear]
    _ = (x ^ 4 - V.b₄ * x ^ 2 - 2 * V.b₆ * x - V.b₈) * ((2 : F) * y) ^ 2 := by
        simp only [b₂, b₄, b₆, b₈, ha1, ha3, zero_mul, mul_zero, sub_zero, add_zero]
        linear_combination (norm := ring_nf)
          (-36 * x ^ 4 - 24 * V.a₄ * x ^ 2 - 4 * V.a₄ ^ 2 - 48 * V.a₂ * x ^ 3
            - 16 * V.a₂ * V.a₄ * x - 16 * V.a₂ ^ 2 * x ^ 2) * e

section PackSigma

variable (ha1 : V.a₁ = 0) (ha3 : V.a₃ = 0) {e₁ e₂ e₃ xq yq d : F}
  (hσ1 : e₁ + e₂ + e₃ = -V.a₂) (hσ2 : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = V.a₄)
  (hσ3 : e₁ * e₂ * e₃ = -V.a₆) (hq : V.toAffine.Equation xq yq)
  (h1 : xq ≠ e₁) (h2 : xq ≠ e₂) (h3 : xq ≠ e₃)
  (hd : d * (4 * xq ^ 3 + V.b₂ * xq ^ 2 + 2 * V.b₄ * xq + V.b₆)
      = xq ^ 4 - V.b₄ * xq ^ 2 - 2 * V.b₆ * xq - V.b₈)

private def xiAt (W' : WeierstrassCurve F) (e xq yq : F) : F :=
  W'.toAffine.addX e xq (W'.toAffine.slope e xq 0 yq)

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 in

private lemma xiAt_closed :
    xiAt V e₁ xq yq = e₁ + (e₁ - e₂) * (e₁ - e₃) / (xq - e₁) ∧
    xiAt V e₂ xq yq = e₂ + (e₂ - e₁) * (e₂ - e₃) / (xq - e₂) ∧
    xiAt V e₃ xq yq = e₃ + (e₃ - e₁) * (e₃ - e₂) / (xq - e₃) := by
  refine ⟨?_, ?_, ?_⟩
  · have t := addX_two_torsion_sub_self ha1 ha3 hσ1 hσ2 hσ3 hq h1
    unfold xiAt
    linear_combination t
  · have hσ1' : e₂ + e₁ + e₃ = -V.a₂ := by linear_combination hσ1
    have hσ2' : e₂ * e₁ + e₂ * e₃ + e₁ * e₃ = V.a₄ := by linear_combination hσ2
    have hσ3' : e₂ * e₁ * e₃ = -V.a₆ := by linear_combination hσ3
    have t := addX_two_torsion_sub_self ha1 ha3 hσ1' hσ2' hσ3' hq h2
    unfold xiAt
    linear_combination t
  · have hσ1' : e₃ + e₁ + e₂ = -V.a₂ := by linear_combination hσ1
    have hσ2' : e₃ * e₁ + e₃ * e₂ + e₁ * e₂ = V.a₄ := by linear_combination hσ2
    have hσ3' : e₃ * e₁ * e₂ = -V.a₆ := by linear_combination hσ3
    have t := addX_two_torsion_sub_self ha1 ha3 hσ1' hσ2' hσ3' hq h3
    unfold xiAt
    linear_combination t

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 hd in

private lemma pack_esymm1 :
    xiAt V e₁ xq yq + xiAt V e₂ xq yq + xiAt V e₃ xq yq + xq = 4 * d := by
  obtain ⟨t1, t2, t3⟩ := xiAt_closed ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3
  have hd1 : xq - e₁ ≠ 0 := sub_ne_zero.mpr h1
  have hd2 : xq - e₂ ≠ 0 := sub_ne_zero.mpr h2
  have hd3 : xq - e₃ ≠ 0 := sub_ne_zero.mpr h3
  rw [t1, t2, t3]
  simp only [b₂, b₄, b₆, b₈, ha1, ha3, zero_mul, mul_zero, sub_zero, add_zero] at hd
  field_simp
  linear_combination (norm := ring_nf)
    (-1) * hd
    + (4 * xq ^ 2 * d + 4 * V.a₆) * hσ1
    + (-4 * xq * d - 2 * xq ^ 2 + e₂ * e₃ + e₁ * e₃ + e₁ * e₂ + V.a₄) * hσ2
    + (4 * d + 8 * xq - 4 * e₃ - 4 * e₂ - 4 * e₁) * hσ3

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 hd in

private lemma pack_esymm2 :
    xiAt V e₁ xq yq * xiAt V e₂ xq yq + xiAt V e₁ xq yq * xiAt V e₃ xq yq
        + xiAt V e₂ xq yq * xiAt V e₃ xq yq
        + xq * (xiAt V e₁ xq yq + xiAt V e₂ xq yq + xiAt V e₃ xq yq)
      = -(V.b₄ + V.b₂ * d) := by
  obtain ⟨t1, t2, t3⟩ := xiAt_closed ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3
  have hd1 : xq - e₁ ≠ 0 := sub_ne_zero.mpr h1
  have hd2 : xq - e₂ ≠ 0 := sub_ne_zero.mpr h2
  have hd3 : xq - e₃ ≠ 0 := sub_ne_zero.mpr h3
  rw [t1, t2, t3]
  simp only [b₂, b₄, b₆, b₈, ha1, ha3, zero_mul, mul_zero, sub_zero, add_zero] at hd ⊢
  field_simp
  linear_combination (norm := ring_nf)
    (-e₃ - e₂ - e₁) * hd
    + (4 * xq ^ 3 * d + 4 * e₂ * e₃ * xq * d + 4 * e₁ * e₃ * xq * d + 4 * e₁ * e₂ * xq * d
      - 4 * e₁ * e₂ * e₃ * d + 4 * V.a₆ * e₃ + 4 * V.a₆ * e₂ + 4 * V.a₆ * e₁) * hσ1
    + (-2 * xq ^ 3 - 4 * e₃ * xq * d - 4 * e₂ * xq * d - 2 * e₂ * e₃ * xq + e₂ * e₃ ^ 2
      + e₂ ^ 2 * e₃ - 4 * e₁ * xq * d - 2 * e₁ * e₃ * xq + e₁ * e₃ ^ 2 - 2 * e₁ * e₂ * xq
      + 5 * e₁ * e₂ * e₃ + e₁ * e₂ ^ 2 + e₁ ^ 2 * e₃ + e₁ ^ 2 * e₂ + V.a₄ * e₃ + V.a₄ * e₂
      + V.a₄ * e₁) * hσ2
    + (4 * e₃ * d + 8 * e₃ * xq - 4 * e₃ ^ 2 + 4 * e₂ * d + 8 * e₂ * xq - 8 * e₂ * e₃ - 4 * e₂ ^ 2
      + 4 * e₁ * d + 8 * e₁ * xq - 8 * e₁ * e₃ - 8 * e₁ * e₂ - 4 * e₁ ^ 2) * hσ3

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 hd in

private lemma pack_esymm3 :
    xiAt V e₁ xq yq * xiAt V e₂ xq yq * xiAt V e₃ xq yq
        + xq * (xiAt V e₁ xq yq * xiAt V e₂ xq yq + xiAt V e₁ xq yq * xiAt V e₃ xq yq
          + xiAt V e₂ xq yq * xiAt V e₃ xq yq)
      = 2 * V.b₆ + 2 * V.b₄ * d := by
  obtain ⟨t1, t2, t3⟩ := xiAt_closed ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3
  have hd1 : xq - e₁ ≠ 0 := sub_ne_zero.mpr h1
  have hd2 : xq - e₂ ≠ 0 := sub_ne_zero.mpr h2
  have hd3 : xq - e₃ ≠ 0 := sub_ne_zero.mpr h3
  rw [t1, t2, t3]
  simp only [b₂, b₄, b₆, b₈, ha1, ha3, zero_mul, mul_zero, sub_zero, add_zero] at hd ⊢
  field_simp
  linear_combination (norm := ring_nf)
    (-e₂ * e₃ - e₁ * e₃ - e₁ * e₂) * hd
    + (4 * e₂ * e₃ * xq ^ 2 * d + 4 * e₁ * e₃ * xq ^ 2 * d + 4 * e₁ * e₂ * xq ^ 2 * d
      + 4 * V.a₆ * e₂ * e₃ + 4 * V.a₆ * e₁ * e₃ + 4 * V.a₆ * e₁ * e₂) * hσ1
    + (4 * xq ^ 3 * d - 4 * e₃ * xq ^ 2 * d - 4 * e₂ * xq ^ 2 * d - 2 * e₂ * e₃ * xq ^ 2
      + e₂ ^ 2 * e₃ ^ 2 - 4 * e₁ * xq ^ 2 * d - 2 * e₁ * e₃ * xq ^ 2 - 2 * e₁ * e₂ * xq ^ 2
      - 4 * e₁ * e₂ * e₃ * d + 2 * e₁ * e₂ * e₃ ^ 2 + 2 * e₁ * e₂ ^ 2 * e₃ + e₁ ^ 2 * e₃ ^ 2
      + 2 * e₁ ^ 2 * e₂ * e₃ + e₁ ^ 2 * e₂ ^ 2 + V.a₄ * e₂ * e₃ + V.a₄ * e₁ * e₃ + V.a₄ * e₁ * e₂) * hσ2
    + (-8 * xq ^ 3 + 8 * e₃ * xq ^ 2 + 8 * e₂ * xq ^ 2 + 4 * e₂ * e₃ * d - 4 * e₂ * e₃ ^ 2
      - 4 * e₂ ^ 2 * e₃ + 8 * e₁ * xq ^ 2 + 4 * e₁ * e₃ * d - 4 * e₁ * e₃ ^ 2 + 4 * e₁ * e₂ * d
      - 4 * e₁ * e₂ * e₃ - 4 * e₁ * e₂ ^ 2 - 4 * e₁ ^ 2 * e₃ - 4 * e₁ ^ 2 * e₂) * hσ3

include ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3 hd in

private lemma pack_esymm4 :
    xiAt V e₁ xq yq * xiAt V e₂ xq yq * xiAt V e₃ xq yq * xq = -(V.b₈ + V.b₆ * d) := by
  obtain ⟨t1, t2, t3⟩ := xiAt_closed ha1 ha3 hσ1 hσ2 hσ3 hq h1 h2 h3
  have hd1 : xq - e₁ ≠ 0 := sub_ne_zero.mpr h1
  have hd2 : xq - e₂ ≠ 0 := sub_ne_zero.mpr h2
  have hd3 : xq - e₃ ≠ 0 := sub_ne_zero.mpr h3
  rw [t1, t2, t3]
  simp only [b₂, b₄, b₆, b₈, ha1, ha3, zero_mul, mul_zero, sub_zero, add_zero] at hd ⊢
  field_simp
  linear_combination (norm := ring_nf)
    (-e₁ * e₂ * e₃) * hd
    + (4 * e₁ * e₂ * e₃ * xq ^ 2 * d + 4 * V.a₆ * xq ^ 3 - 4 * V.a₆ * e₃ * xq ^ 2
      - 4 * V.a₆ * e₂ * xq ^ 2 + 4 * V.a₆ * e₂ * e₃ * xq - 4 * V.a₆ * e₁ * xq ^ 2
      + 4 * V.a₆ * e₁ * e₃ * xq + 4 * V.a₆ * e₁ * e₂ * xq) * hσ1
    + (e₂ * e₃ * xq ^ 3 - e₂ * e₃ ^ 2 * xq ^ 2 - e₂ ^ 2 * e₃ * xq ^ 2 + e₂ ^ 2 * e₃ ^ 2 * xq
      + e₁ * e₃ * xq ^ 3 - e₁ * e₃ ^ 2 * xq ^ 2 + e₁ * e₂ * xq ^ 3 - 4 * e₁ * e₂ * e₃ * xq * d
      - 5 * e₁ * e₂ * e₃ * xq ^ 2 + 2 * e₁ * e₂ * e₃ ^ 2 * xq - e₁ * e₂ ^ 2 * xq ^ 2
      + 2 * e₁ * e₂ ^ 2 * e₃ * xq - e₁ ^ 2 * e₃ * xq ^ 2 + e₁ ^ 2 * e₃ ^ 2 * xq
      - e₁ ^ 2 * e₂ * xq ^ 2 + 2 * e₁ ^ 2 * e₂ * e₃ * xq + e₁ ^ 2 * e₂ ^ 2 * xq + V.a₄ * xq ^ 3
      - V.a₄ * e₃ * xq ^ 2 - V.a₄ * e₂ * xq ^ 2 + V.a₄ * e₂ * e₃ * xq - V.a₄ * e₁ * xq ^ 2
      + V.a₄ * e₁ * e₃ * xq + V.a₄ * e₁ * e₂ * xq) * hσ2
    + (4 * xq ^ 3 * d - 4 * e₃ * xq ^ 2 * d - 4 * e₃ * xq ^ 3 + 4 * e₃ ^ 2 * xq ^ 2
      - 4 * e₂ * xq ^ 2 * d - 4 * e₂ * xq ^ 3 + 4 * e₂ * e₃ * xq * d + 8 * e₂ * e₃ * xq ^ 2
      - 4 * e₂ * e₃ ^ 2 * xq + 4 * e₂ ^ 2 * xq ^ 2 - 4 * e₂ ^ 2 * e₃ * xq - 4 * e₁ * xq ^ 2 * d
      - 4 * e₁ * xq ^ 3 + 4 * e₁ * e₃ * xq * d + 8 * e₁ * e₃ * xq ^ 2 - 4 * e₁ * e₃ ^ 2 * xq
      + 4 * e₁ * e₂ * xq * d + 8 * e₁ * e₂ * xq ^ 2 - 4 * e₁ * e₂ * e₃ * xq - 4 * e₁ * e₂ ^ 2 * xq
      + 4 * e₁ ^ 2 * xq ^ 2 - 4 * e₁ ^ 2 * e₃ * xq - 4 * e₁ ^ 2 * e₂ * xq) * hσ3

end PackSigma

private lemma image_fold2_Icc (n : ℕ) : (Finset.Icc 1 n).image (fold2 n) = Finset.Icc 1 n := by
  apply Finset.eq_of_subset_of_card_le
  · intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    exact fold2_mem hk
  · rw [Finset.card_image_of_injOn (fun k hk k' hk' h => by
      have := congrArg (unfold2 n) h
      rwa [unfold2_fold2 hk, unfold2_fold2 hk'] at this)]

private lemma multiset_map_double {Q : V.toAffine.Point} {n : ℕ} (hQ : addOrderOf Q = 2 * n + 1) :
    (Finset.Icc 1 n).val.map (fun k => ((2 : ℕ) • (k • Q)).coordsOrZero.1)
      = (Finset.Icc 1 n).val.map (fun k => ((k : ℕ) • Q).coordsOrZero.1) := by
  have hstep : ∀ k ∈ (Finset.Icc 1 n).val,
      ((2 : ℕ) • (k • Q)).coordsOrZero.1 = ((fold2 n k • Q).coordsOrZero).1 := by
    intro k hk
    rw [coordsOrZero_fold2_smul_fst hQ (by simpa using hk), smul_smul]
  rw [Multiset.map_congr rfl hstep]
  have himg : (Finset.Icc 1 n).val.map (fold2 n) = (Finset.Icc 1 n).val := by
    have hinj : Set.InjOn (fold2 n) (Finset.Icc 1 n) := fun k hk k' hk' h => by
      have := congrArg (unfold2 n) h
      rwa [unfold2_fold2 (by simpa using hk), unfold2_fold2 (by simpa using hk')] at this
    rw [← Finset.image_val_of_injOn hinj, image_fold2_Icc]
  calc (Finset.Icc 1 n).val.map (fun k => ((fold2 n k • Q).coordsOrZero).1)
      = ((Finset.Icc 1 n).val.map (fold2 n)).map (fun m => ((m • Q).coordsOrZero).1) := by
        rw [Multiset.map_map]; rfl
    _ = (Finset.Icc 1 n).val.map (fun m => ((m • Q).coordsOrZero).1) := by rw [himg]

end Pack

section Trace

variable {V : WeierstrassCurve F} {Q : V.toAffine.Point} {n : ℕ}

private def xvSum (V : WeierstrassCurve F) (Q : V.toAffine.Point) (n : ℕ) (v : F) : F :=
  v + ∑ k ∈ Finset.Icc 1 n,
    (V.veluT ((k • Q).coordsOrZero).1 ((k • Q).coordsOrZero).2 / (v - ((k • Q).coordsOrZero).1)
      + V.veluU ((k • Q).coordsOrZero).1 ((k • Q).coordsOrZero).2
          / (v - ((k • Q).coordsOrZero).1) ^ 2)

private def orbitTrace (V : WeierstrassCurve F) (Q : V.toAffine.Point) (n : ℕ)
    (P : V.toAffine.Point) : F :=
  ∑ j ∈ Finset.range (2 * n + 1), ((P + j • Q).coordsOrZero).1

private lemma orbitTrace_add_right (hQ : addOrderOf Q = 2 * n + 1) (P : V.toAffine.Point) :
    orbitTrace V Q n (P + Q) = orbitTrace V Q n P := by
  have hN : (2 * n + 1) • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  unfold orbitTrace
  have key : ∀ j : ℕ, P + Q + j • Q = P + (j + 1) • Q := by
    intro j
    rw [succ_nsmul]
    abel
  simp only [key]
  have h1 := Finset.sum_range_succ' (fun j => ((P + j • Q).coordsOrZero).1) (2 * n + 1)
  have h2 := Finset.sum_range_succ (fun j => ((P + j • Q).coordsOrZero).1) (2 * n + 1)
  have hf : ((P + (2 * n + 1) • Q).coordsOrZero).1 = ((P + 0 • Q).coordsOrZero).1 := by
    rw [hN, zero_nsmul]
  have hcomb := h1.symm.trans h2
  rw [hf] at hcomb
  simpa using add_right_cancel hcomb

private lemma orbitTrace_add_smul (hQ : addOrderOf Q = 2 * n + 1) (P : V.toAffine.Point) (m : ℕ) :
    orbitTrace V Q n (P + m • Q) = orbitTrace V Q n P := by
  induction m with
  | zero => rw [zero_nsmul, add_zero]
  | succ m ih =>
    have : P + (m + 1) • Q = P + m • Q + Q := by rw [succ_nsmul]; abel
    rw [this, orbitTrace_add_right hQ, ih]

private lemma orbitTrace_fold (hQ : addOrderOf Q = 2 * n + 1) (P : V.toAffine.Point) :
    orbitTrace V Q n P = (P.coordsOrZero).1
      + ∑ k ∈ Finset.Icc 1 n,
          (((P + k • Q).coordsOrZero).1 + ((P - k • Q).coordsOrZero).1) := by
  unfold orbitTrace
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive (fun j => ((P + j • Q).coordsOrZero).1)
      (by omega : (0 : ℕ) ≤ n + 1) (by omega : n + 1 ≤ 2 * n + 1),
    ← Finset.sum_Ico_consecutive (fun j => ((P + j • Q).coordsOrZero).1)
      (by omega : (0 : ℕ) ≤ 1) (by omega : (1 : ℕ) ≤ n + 1)]
  have hA : ∑ j ∈ Finset.Ico 0 1, ((P + j • Q).coordsOrZero).1 = (P.coordsOrZero).1 := by
    simp
  have hB : ∑ j ∈ Finset.Ico 1 (n + 1), ((P + j • Q).coordsOrZero).1
      = ∑ k ∈ Finset.Icc 1 n, ((P + k • Q).coordsOrZero).1 := by
    have hset : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := by
      ext m
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hset]
  have hC : ∑ j ∈ Finset.Ico (n + 1) (2 * n + 1), ((P + j • Q).coordsOrZero).1
      = ∑ k ∈ Finset.Icc 1 n, ((P - k • Q).coordsOrZero).1 := by
    refine Finset.sum_nbij' (fun j => 2 * n + 1 - j) (fun k => 2 * n + 1 - k)
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_Icc]
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_Ico]
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      rw [sub_smul_eq_neg_smul hQ (show j ≤ 2 * n + 1 by omega), sub_neg_eq_add]
  rw [hA, hB, hC, add_assoc, ← Finset.sum_add_distrib]

end Trace

end N5IDAux4

namespace N5IDAux1

open Polynomial Finset

section Reflect

variable {R : Type*} [CommRing R]

private theorem reflect_sum' {ι : Type*} (s : Finset ι) (p : ι → R[X]) (N : ℕ) :
    reflect N (∑ q ∈ s, p q) = ∑ q ∈ s, reflect N (p q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, reflect_add, ih]

private theorem reflect_prod_le {ι : Type*} (s : Finset ι) (p : ι → R[X]) (b : ℕ)
    (hb : ∀ q ∈ s, (p q).natDegree ≤ b) :
    reflect (s.card * b) (∏ q ∈ s, p q) = ∏ q ∈ s, reflect b (p q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha,
      show (s.card + 1) * b = b + s.card * b by ring]
    have hbs : (∏ q ∈ s, p q).natDegree ≤ s.card * b := by
      refine (natDegree_prod_le _ _).trans ?_
      calc ∑ i ∈ s, (p i).natDegree ≤ ∑ _i ∈ s, b :=
            sum_le_sum fun i hi => hb i (mem_insert_of_mem hi)
        _ = s.card * b := by simp
    rw [reflect_mul _ _ (hb a (mem_insert_self a s)) hbs,
      ih fun q hq => hb q (mem_insert_of_mem hq)]

private theorem reflect_pow_le (p : R[X]) (b k : ℕ) (hb : p.natDegree ≤ b) :
    reflect (k * b) (p ^ k) = reflect b p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, show (k + 1) * b = k * b + b by ring,
      reflect_mul _ _ ((natDegree_pow_le).trans (Nat.mul_le_mul_left k hb)) hb, ih]

private theorem reflect_X_sub_C (a : R) : reflect 1 (X - C a) = 1 - C a * X := by
  rw [reflect_sub, reflect_one_X, reflect_C, pow_one]

private theorem natDegree_sub_le_of_le' {p q : R[X]} {n : ℕ} (hp : p.natDegree ≤ n)
    (hq : q.natDegree ≤ n) : (p - q).natDegree ≤ n :=
  (natDegree_sub_le_of_le hp hq).trans (max_le le_rfl le_rfl)

private theorem natDegree_X_sub_C_le' (a : R) : (X - C a : R[X]).natDegree ≤ 1 :=
  natDegree_sub_le_of_le' natDegree_X_le ((natDegree_C a).le.trans zero_le_one)

end Reflect

variable {K : Type*} [Field K]

section Defs
variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → K)

private noncomputable def hP : K[X] := ∏ q ∈ S, (X - C (x q))

private noncomputable def AP : K[X] :=
  X * hP S x ^ 2 +
    ∑ q ∈ S, (C (t q) * (X - C (x q)) + C (u q)) * ∏ q' ∈ S.erase q, (X - C (x q')) ^ 2

end Defs

private noncomputable def fP (b₂ b₄ b₆ : K) : K[X] :=
  C 4 * X ^ 3 + C b₂ * X ^ 2 + C (2 * b₄) * X + C b₆

private noncomputable def φP (b₄ b₆ b₈ : K) : K[X] :=
  X ^ 4 - C b₄ * X ^ 2 - C (2 * b₆) * X - C b₈

private abbrev R4 (K : Type*) [Field K] := K[X] ⧸ Ideal.span {(X : K[X]) ^ 4}

private noncomputable abbrev π : K[X] →+* R4 K := Ideal.Quotient.mk _

private theorem π_X_pow_four : (π (X : K[X])) ^ 4 = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

private theorem eq_of_π_eq {p q : K[X]} (hp : p.natDegree ≤ 3) (hq : q.natDegree ≤ 3)
    (h : π p = π q) : p = q := by
  have hmem : (X : K[X]) ^ 4 ∣ p - q := by
    rw [← Ideal.mem_span_singleton]
    exact Ideal.Quotient.eq.mp h
  have hzero : p - q = 0 := by
    refine eq_zero_of_dvd_of_natDegree_lt hmem ?_
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt (natDegree_sub_le_of_le' hp hq) (by norm_num)
  exact sub_eq_zero.mp hzero

private theorem prod_eq_of_map_eq {ι β : Type*} {M : Type*} [CommMonoid M] (S : Finset ι)
    {d x : ι → β} (hperm : S.val.map d = S.val.map x) (g : β → M) :
    ∏ q ∈ S, g (d q) = ∏ q ∈ S, g (x q) := by
  have h1 : ∏ q ∈ S, g (d q) = ((S.val.map d).map g).prod := by
    rw [Multiset.map_map]; rfl
  have h2 : ∏ q ∈ S, g (x q) = ((S.val.map x).map g).prod := by
    rw [Multiset.map_map]; rfl
  rw [h1, h2, hperm]

private theorem prod_one_add_sq_mul {ι : Type*} {A : Type*} [CommRing A] (S : Finset ι) (ε : A)
    (hε : ε ^ 4 = 0) (y : ι → A) :
    ∏ q ∈ S, (1 + ε ^ 2 * y q) = 1 + ε ^ 2 * ∑ q ∈ S, y q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, ih]
    linear_combination (y a * ∑ q ∈ s, y q) * hε

private noncomputable def eps (K : Type*) [Field K] : R4 K := π (X : K[X])

private theorem eps_pow_four : (eps K) ^ 4 = 0 := π_X_pow_four

private theorem π_X : π (X : K[X]) = eps K := rfl

private noncomputable def sc {K : Type*} [Field K] : K →+* R4 K := (π : K[X] →+* R4 K).comp C

private theorem π_C (a : K) : π (C a) = sc a := rfl

section Trunc

variable {A : Type*} [CommRing A] {ε : A}

private theorem trunc_unit (hε : ε ^ 4 = 0) (a : A) :
    (1 - a * ε) * (1 + a * ε + a ^ 2 * ε ^ 2 + a ^ 3 * ε ^ 3) = 1 := by
  linear_combination (-a ^ 4) * hε

private theorem trunc_pow8 (hε : ε ^ 4 = 0) (a : A) :
    (1 - a * ε) ^ 8 = 1 - 8 * a * ε + 28 * a ^ 2 * ε ^ 2 - 56 * a ^ 3 * ε ^ 3 := by
  linear_combination (70 * a ^ 4 - 56 * a ^ 5 * ε + 28 * a ^ 6 * ε ^ 2
    - 8 * a ^ 7 * ε ^ 3 + a ^ 8 * ε ^ 4) * hε

private theorem trunc_perq (hε : ε ^ 4 = 0) (a b₂ b₄ b₆ : A) :
    (1 - 4 * a * ε - (b₄ + b₂ * a) * ε ^ 2 - (2 * b₆ + 2 * b₄ * a) * ε ^ 3) ^ 2
      = (1 - a * ε) ^ 8 * (1 + ε ^ 2 * (-2 * (6 * a ^ 2 + b₂ * a + b₄)
          - 4 * (10 * a ^ 3 + 2 * b₂ * a ^ 2 + 3 * b₄ * a + b₆) * ε)) := by
  rw [trunc_pow8 hε]
  linear_combination (b₄ ^ 2 + 4 * ε * b₄ * b₆ + 4 * ε ^ 2 * b₆ ^ 2
    - 16 * a * b₆ + 2 * a * b₂ * b₄ + 4 * a * ε * b₄ ^ 2
    + 4 * a * ε * b₂ * b₆ + 8 * a * ε ^ 2 * b₄ * b₆ - 24 * a ^ 2 * b₄
    + a ^ 2 * b₂ ^ 2 + 112 * a ^ 2 * ε * b₆ + 4 * a ^ 2 * ε * b₂ * b₄
    + 4 * a ^ 2 * ε ^ 2 * b₄ ^ 2 - 8 * a ^ 3 * b₂ + 224 * a ^ 3 * ε * b₄
    - 224 * a ^ 3 * ε ^ 2 * b₆ + 16 * a ^ 4 + 112 * a ^ 4 * ε * b₂
    - 672 * a ^ 4 * ε ^ 2 * b₄ + 448 * a ^ 5 * ε - 448 * a ^ 5 * ε ^ 2 * b₂
    - 2240 * a ^ 6 * ε ^ 2) * hε

private theorem trunc_lhs (hε : ε ^ 4 = 0) (η T W c₂ c₁ c₀ : A) :
    4 * (η ^ 2 * (1 + T * ε ^ 2 + W * ε ^ 3)) ^ 3
      + c₂ * ε * (η ^ 2 * (1 + T * ε ^ 2 + W * ε ^ 3)) ^ 2 * η ^ 2
      + c₁ * ε ^ 2 * (η ^ 2 * (1 + T * ε ^ 2 + W * ε ^ 3)) * η ^ 4 + c₀ * ε ^ 3 * η ^ 6
      = η ^ 6 * (4 + c₂ * ε + (12 * T + c₁) * ε ^ 2
          + (12 * W + 2 * c₂ * T + c₀) * ε ^ 3) := by
  linear_combination (η ^ 6 * (2 * W * c₂ + T * c₁ + 12 * T ^ 2
    + ε * W * c₁ + 24 * ε * T * W + ε * T ^ 2 * c₂ + 12 * ε ^ 2 * W ^ 2
    + 2 * ε ^ 2 * T * W * c₂ + 4 * ε ^ 2 * T ^ 3 + ε ^ 3 * W ^ 2 * c₂
    + 12 * ε ^ 3 * T ^ 2 * W + 12 * ε ^ 4 * T * W ^ 2 + 4 * ε ^ 5 * W ^ 3)) * hε

private theorem trunc_alpha_summand (hε : ε ^ 4 = 0) (P a t u : A) :
    (t * (1 - a * ε) + u * ε) * P * ε ^ 2
      = P * (1 - a * ε) ^ 2 * (t * ε ^ 2 + (u + a * t) * ε ^ 3) := by
  linear_combination (P * (2 * a * (u + a * t) - a ^ 2 * t - a ^ 2 * (u + a * t) * ε)) * hε

private theorem trunc_phi (hε : ε ^ 4 = 0) (b₂ b₄ b₆ T W : A) :
    (4 + b₂ * ε + 2 * b₄ * ε ^ 2 + b₆ * ε ^ 3) * (1 + ε ^ 2 * (-2 * T - 4 * W * ε))
      = 4 + b₂ * ε + (2 * b₄ - 8 * T) * ε ^ 2 + (b₆ - 2 * b₂ * T - 16 * W) * ε ^ 3 := by
  linear_combination (-4 * b₄ * T - 4 * b₂ * W - 2 * ε * b₆ * T - 8 * ε * b₄ * W
    - 4 * ε ^ 2 * b₆ * W) * hε

private theorem trunc_num (hε : ε ^ 4 = 0) (a b₂ b₄ b₆ b₈ : A) :
    (1 * ε ^ 0 - b₄ * ε ^ 2 - 2 * b₆ * ε ^ 3 - b₈ * ε ^ 4)
      - a * (4 * ε ^ 1 + b₂ * ε ^ 2 + 2 * b₄ * ε ^ 3 + b₆ * ε ^ 4)
      = 1 - 4 * a * ε - (b₄ + b₂ * a) * ε ^ 2 - (2 * b₆ + 2 * b₄ * a) * ε ^ 3 := by
  linear_combination (-b₈ - a * b₆) * hε

end Trunc

set_option maxHeartbeats 4000000 in

private theorem expansion_core {ι : Type*} [DecidableEq ι] (S : Finset ι) (x d t u : ι → K)
    (b₂ b₄ b₆ b₈ c₂ c₁ c₀ : K)
    (ht : ∀ q ∈ S, t q = 6 * x q ^ 2 + b₂ * x q + b₄)
    (hu : ∀ q ∈ S, u q = 4 * x q ^ 3 + b₂ * x q ^ 2 + 2 * b₄ * x q + b₆)
    (hperm : S.val.map d = S.val.map x)
    (Ar hr fr : K[X]) (mr : ι → K[X])
    (Hhr : hr = ∏ q ∈ S, (1 - C (x q) * X))
    (HAr : Ar = hr ^ 2 + ∑ q ∈ S, (C (t q) * (1 - C (x q) * X) + C (u q) * X)
      * (∏ q' ∈ S.erase q, (1 - C (x q') * X) ^ 2) * X ^ 2)
    (Hfr : fr = C 4 + C b₂ * X + C (2 * b₄) * X ^ 2 + C b₆ * X ^ 3)
    (Hmr : ∀ q ∈ S, mr q * (1 - C (x q) * X)
      = (C 1 * X ^ 0 - C b₄ * X ^ 2 - C (2 * b₆) * X ^ 3 - C b₈ * X ^ 4)
        - C (d q) * (C 4 * X ^ 1 + C b₂ * X ^ 2 + C (2 * b₄) * X ^ 3 + C b₆ * X ^ 4))
    (R : C 4 * Ar ^ 3 + C c₂ * X * Ar ^ 2 * hr ^ 2 + C c₁ * X ^ 2 * Ar * hr ^ 4
      + C c₀ * X ^ 3 * hr ^ 6 = fr * ∏ q ∈ S, mr q ^ 2) :
    c₂ = b₂ ∧ c₁ = 2 * b₄ - 20 * ∑ q ∈ S, t q
      ∧ c₀ = b₆ - 4 * b₂ * (∑ q ∈ S, t q) - 28 * ∑ q ∈ S, (u q + x q * t q) := by
  obtain ⟨ε, hεdef⟩ : ∃ e : R4 K, e = eps K := ⟨_, rfl⟩
  have hε : ε ^ 4 = 0 := by rw [hεdef]; exact eps_pow_four
  set tK : K := ∑ q ∈ S, t q with htK
  set wK : K := ∑ q ∈ S, (u q + x q * t q) with hwK

  have Eη : π hr = ∏ q ∈ S, (1 - sc (x q) * ε) := by
    rw [Hhr, map_prod]
    refine prod_congr rfl fun q _ => ?_
    rw [map_sub, map_one, map_mul, π_C, π_X, ← hεdef]
  have Eφ : π fr = 4 + sc b₂ * ε + 2 * sc b₄ * ε ^ 2 + sc b₆ * ε ^ 3 := by
    rw [Hfr]
    simp only [map_add, map_mul, map_pow, π_C, π_X, map_ofNat, ← hεdef]
  have hηunit : IsUnit (π hr) := by
    rw [Eη]
    refine prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun q _ => ?_
    exact IsUnit.of_mul_eq_one _ (trunc_unit hε (sc (x q)))

  have eP : ∀ q ∈ S, (∏ q' ∈ S.erase q, (1 - sc (x q') * ε) ^ 2) * (1 - sc (x q) * ε) ^ 2
      = π hr ^ 2 := by
    intro q hq
    rw [Eη, ← prod_pow]
    exact prod_erase_mul S (fun q' => (1 - sc (x q') * ε) ^ 2) hq
  have Eα : π Ar = π hr ^ 2 * (1 + sc tK * ε ^ 2 + sc wK * ε ^ 3) := by
    have e0 : π Ar = π hr ^ 2 + ∑ q ∈ S, (sc (t q) * (1 - sc (x q) * ε) + sc (u q) * ε)
        * (∏ q' ∈ S.erase q, (1 - sc (x q') * ε) ^ 2) * ε ^ 2 := by
      rw [HAr]
      simp only [map_add, map_sub, map_mul, map_pow, map_sum, map_prod, map_one, π_C, π_X,
        ← hεdef]
    have e1 : ∀ q ∈ S, (sc (t q) * (1 - sc (x q) * ε) + sc (u q) * ε)
        * (∏ q' ∈ S.erase q, (1 - sc (x q') * ε) ^ 2) * ε ^ 2
        = π hr ^ 2 * (sc (t q) * ε ^ 2 + sc (u q + x q * t q) * ε ^ 3) := by
      intro q hq
      rw [trunc_alpha_summand hε, eP q hq, map_add, map_mul]
    rw [e0, sum_congr rfl e1, ← mul_sum, sum_add_distrib, ← sum_mul, ← sum_mul,
      ← map_sum, ← map_sum, ← htK, ← hwK]
    ring

  have ELHS : π (C 4) * π Ar ^ 3 + π (C c₂) * ε * π Ar ^ 2 * π hr ^ 2
      + π (C c₁) * ε ^ 2 * π Ar * π hr ^ 4 + π (C c₀) * ε ^ 3 * π hr ^ 6
      = π hr ^ 6 * (4 + sc c₂ * ε + (12 * sc tK + sc c₁) * ε ^ 2
          + (12 * sc wK + 2 * sc c₂ * sc tK + sc c₀) * ε ^ 3) := by
    rw [Eα, π_C, π_C, π_C, π_C, map_ofNat]
    exact trunc_lhs hε _ _ _ _ _ _

  have Eμ : ∀ q ∈ S, π (mr q) * (1 - sc (x q) * ε)
      = 1 - 4 * sc (d q) * ε - (sc b₄ + sc b₂ * sc (d q)) * ε ^ 2
        - (2 * sc b₆ + 2 * sc b₄ * sc (d q)) * ε ^ 3 := by
    intro q hq
    have e := congrArg π (Hmr q hq)
    simp only [map_sub, map_add, map_mul, map_pow, map_one, π_C, π_X, map_ofNat,
      ← hεdef] at e
    rw [e]
    exact trunc_num hε _ _ _ _ _
  have ERHS : (π fr * ∏ q ∈ S, π (mr q) ^ 2) * π hr ^ 2
      = π fr * π hr ^ 8 * (1 + ε ^ 2 * (-2 * sc tK - 4 * sc wK * ε)) := by
    have e1 : (∏ q ∈ S, π (mr q) ^ 2) * π hr ^ 2
        = ∏ q ∈ S, (π (mr q) * (1 - sc (x q) * ε)) ^ 2 := by
      rw [Eη, ← prod_pow, ← prod_mul_distrib]
      exact prod_congr rfl fun q _ => by ring
    have e2 : ∏ q ∈ S, (π (mr q) * (1 - sc (x q) * ε)) ^ 2
        = ∏ q ∈ S, ((1 - sc (d q) * ε) ^ 8
            * (1 + ε ^ 2 * (-2 * (6 * sc (d q) ^ 2 + sc b₂ * sc (d q) + sc b₄)
              - 4 * (10 * sc (d q) ^ 3 + 2 * sc b₂ * sc (d q) ^ 2 + 3 * sc b₄ * sc (d q) + sc b₆) * ε))) :=
      prod_congr rfl fun q hq => by rw [Eμ q hq, trunc_perq hε]
    have e3 : ∏ q ∈ S, ((1 - sc (d q) * ε) ^ 8
            * (1 + ε ^ 2 * (-2 * (6 * sc (d q) ^ 2 + sc b₂ * sc (d q) + sc b₄)
              - 4 * (10 * sc (d q) ^ 3 + 2 * sc b₂ * sc (d q) ^ 2 + 3 * sc b₄ * sc (d q) + sc b₆) * ε)))
        = π hr ^ 8 * (1 + ε ^ 2 * ∑ q ∈ S, (-2 * (6 * sc (x q) ^ 2 + sc b₂ * sc (x q) + sc b₄)
              - 4 * (10 * sc (x q) ^ 3 + 2 * sc b₂ * sc (x q) ^ 2 + 3 * sc b₄ * sc (x q) + sc b₆) * ε)) := by
      have p1 := prod_eq_of_map_eq S hperm (fun a => (1 - sc a * ε) ^ 8)
      have p2 := prod_eq_of_map_eq S hperm (fun a => 1 + ε ^ 2 * (-2 * (6 * sc (a) ^ 2 + sc b₂ * sc (a) + sc b₄)
              - 4 * (10 * sc (a) ^ 3 + 2 * sc b₂ * sc (a) ^ 2 + 3 * sc b₄ * sc (a) + sc b₆) * ε))
      rw [prod_mul_distrib, p1, p2, prod_one_add_sq_mul S ε hε, Eη, prod_pow]
    have e4 : ∑ q ∈ S, (-2 * (6 * sc (x q) ^ 2 + sc b₂ * sc (x q) + sc b₄)
              - 4 * (10 * sc (x q) ^ 3 + 2 * sc b₂ * sc (x q) ^ 2 + 3 * sc b₄ * sc (x q) + sc b₆) * ε) = -2 * sc tK - 4 * sc wK * ε := by
      have e5 : ∀ q ∈ S, (-2 * (6 * sc (x q) ^ 2 + sc b₂ * sc (x q) + sc b₄)
              - 4 * (10 * sc (x q) ^ 3 + 2 * sc b₂ * sc (x q) ^ 2 + 3 * sc b₄ * sc (x q) + sc b₆) * ε)
          = -2 * sc (t q) - 4 * sc (u q + x q * t q) * ε := by
        intro q hq
        rw [ht q hq, hu q hq]
        simp only [map_add, map_mul, map_pow, map_ofNat]
        ring
      rw [sum_congr rfl e5, sum_sub_distrib, ← mul_sum, ← sum_mul, ← mul_sum, ← map_sum,
        ← map_sum, ← htK, ← hwK]
    rw [mul_assoc, e1, e2, e3, e4]
    ring

  have Rπ := congrArg (fun z => π z * π hr ^ 2) R
  simp only [map_add, map_mul, map_pow, map_prod, π_X, ← hεdef] at Rπ
  rw [ELHS, ERHS] at Rπ
  have main : π hr ^ 8 * (4 + sc c₂ * ε + (12 * sc tK + sc c₁) * ε ^ 2
      + (12 * sc wK + 2 * sc c₂ * sc tK + sc c₀) * ε ^ 3)
      = π hr ^ 8 * (π fr * (1 + ε ^ 2 * (-2 * sc tK - 4 * sc wK * ε))) := by
    linear_combination Rπ
  have main2 := (hηunit.pow 8).mul_left_cancel main
  rw [Eφ, trunc_phi hε] at main2

  have final : π (C 4 + C c₂ * X + C (12 * tK + c₁) * X ^ 2
      + C (12 * wK + 2 * c₂ * tK + c₀) * X ^ 3)
      = π (C 4 + C b₂ * X + C (2 * b₄ - 8 * tK) * X ^ 2
      + C (b₆ - 2 * b₂ * tK - 16 * wK) * X ^ 3) := by
    simp only [map_add, map_sub, map_mul, map_pow, π_C, π_X, map_ofNat, ← hεdef]
    exact main2
  have hdeg3 : ∀ a₀ a₁ a₂ a₃ : K,
      (C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 : K[X]).natDegree ≤ 3 := by
    intro a₀ a₁ a₂ a₃
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (by simp) ?_) ?_) ?_
    · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by norm_num))
    · exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le_of_le 2 natDegree_X_le).trans
        (by norm_num))
    · exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le_of_le 3 natDegree_X_le)
  have poly_eq := eq_of_π_eq (hdeg3 _ _ _ _) (hdeg3 _ _ _ _) final
  have k1 := congrArg (fun p : K[X] => p.coeff 1) poly_eq
  have k2 := congrArg (fun p : K[X] => p.coeff 2) poly_eq
  have k3 := congrArg (fun p : K[X] => p.coeff 3) poly_eq
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at k1 k2 k3
  norm_num at k1 k2 k3
  refine ⟨k1, ?_, ?_⟩
  · linear_combination k2
  · linear_combination k3 - 2 * tK * k1

section ReflectAtoms

variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x d t u : ι → K)

omit [DecidableEq ι] in
private theorem natDegree_hP_le : (hP S x).natDegree ≤ S.card := by
  rw [hP]
  refine (natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul S (fun i => (X - C (x i) : K[X]).natDegree) 1
    fun i _ => natDegree_X_sub_C_le' (x i)).trans ?_
  simp

omit [DecidableEq ι] in
private theorem natDegree_lin_le (q : ι) : (C (t q) * (X - C (x q)) + C (u q) : K[X]).natDegree ≤ 1 :=
  natDegree_add_le_of_degree_le
    ((natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le' _)) (by simp)

private theorem natDegree_Pq_le (q : ι) :
    (∏ q' ∈ S.erase q, (X - C (x q')) ^ 2 : K[X]).natDegree ≤ (S.erase q).card * 2 := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i ∈ S.erase q, ((X - C (x i)) ^ 2 : K[X]).natDegree ≤ ∑ _i ∈ S.erase q, 2 :=
        sum_le_sum fun i _ => (natDegree_pow_le).trans (by
          have := natDegree_X_sub_C_le' (R := K) (x i); omega)
    _ = (S.erase q).card * 2 := by simp

private theorem natDegree_AP_le : (AP S x t u).natDegree ≤ 2 * S.card + 1 := by
  rw [AP]
  refine natDegree_add_le_of_degree_le ?_ ?_
  · refine (natDegree_mul_le).trans ?_
    have h2 : (hP S x ^ 2).natDegree ≤ 2 * S.card :=
      (natDegree_pow_le).trans (Nat.mul_le_mul_left 2 (natDegree_hP_le S x))
    have := natDegree_X_le (R := K)
    omega
  · refine natDegree_sum_le_of_forall_le _ _ fun q hq => ?_
    refine (natDegree_mul_le).trans ?_
    have h1 := natDegree_lin_le x t u q
    have h2 := natDegree_Pq_le S x q
    have h3 : (S.erase q).card + 1 = S.card := card_erase_add_one hq
    omega

private theorem natDegree_fP_le (b₂ b₄ b₆ : K) : (fP b₂ b₄ b₆).natDegree ≤ 3 := by
  rw [fP]
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le ?_ ?_) ?_) ?_
  · exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le_of_le 3 natDegree_X_le)
  · exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le_of_le 2 natDegree_X_le).trans
      (by norm_num))
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by norm_num))
  · simp

private theorem natDegree_φP_le (b₄ b₆ b₈ : K) : (φP b₄ b₆ b₈ : K[X]).natDegree ≤ 4 := by
  rw [φP]
  refine natDegree_sub_le_of_le' (natDegree_sub_le_of_le' (natDegree_sub_le_of_le' ?_ ?_) ?_) ?_
  · exact natDegree_pow_le_of_le 4 natDegree_X_le
  · exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le_of_le 2 natDegree_X_le).trans
      (by norm_num))
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by norm_num))
  · simp

omit [DecidableEq ι] in
private theorem natDegree_m_le (m : ι → K[X]) (b₂ b₄ b₆ b₈ : K)
    (hm : ∀ q ∈ S, m q * (X - C (x q)) = φP b₄ b₆ b₈ - C (d q) * fP b₂ b₄ b₆) :
    ∀ q ∈ S, (m q).natDegree ≤ 3 := by
  intro q hq
  by_cases hm0 : m q = 0
  · simp [hm0]
  have hXC : (X - C (x q) : K[X]) ≠ 0 := X_sub_C_ne_zero _
  have key := congrArg natDegree (hm q hq)
  rw [natDegree_mul hm0 hXC, natDegree_X_sub_C] at key
  have : (φP b₄ b₆ b₈ - C (d q) * fP b₂ b₄ b₆ : K[X]).natDegree ≤ 4 :=
    natDegree_sub_le_of_le' (natDegree_φP_le b₄ b₆ b₈) ((natDegree_C_mul_le _ _).trans
      ((natDegree_fP_le b₂ b₄ b₆).trans (by norm_num)))
  omega

private theorem reflect_sq (a : K) : reflect 2 ((X - C a) ^ 2) = (1 - C a * X) ^ 2 := by
  have e := reflect_pow_le (X - C a) 1 2 (natDegree_X_sub_C_le' a)
  rw [mul_one] at e
  rw [e, reflect_X_sub_C]

omit [DecidableEq ι] in
private theorem reflect_hP : reflect S.card (hP S x) = ∏ q ∈ S, (1 - C (x q) * X) := by
  have e := reflect_prod_le S (fun q => (X - C (x q) : K[X])) 1
    (fun q _ => natDegree_X_sub_C_le' _)
  rw [mul_one] at e
  rw [hP, e]
  exact prod_congr rfl fun q _ => reflect_X_sub_C _

private theorem reflect_AP : reflect (2 * S.card + 1) (AP S x t u) = reflect S.card (hP S x) ^ 2
    + ∑ q ∈ S, (C (t q) * (1 - C (x q) * X) + C (u q) * X)
      * (∏ q' ∈ S.erase q, (1 - C (x q') * X) ^ 2) * X ^ 2 := by
  have hdeg_h := natDegree_hP_le S x
  have hdeg_h2 : (hP S x ^ 2).natDegree ≤ 2 * S.card :=
    (natDegree_pow_le).trans (Nat.mul_le_mul_left 2 hdeg_h)
  rw [AP, reflect_add]
  congr 1
  · rw [show 2 * S.card + 1 = 1 + 2 * S.card by ring, reflect_mul _ _ natDegree_X_le hdeg_h2,
      reflect_one_X, one_mul, reflect_pow_le _ _ 2 hdeg_h]
  · rw [reflect_sum']
    refine sum_congr rfl fun q hq => ?_
    have hk : (S.erase q).card + 1 = S.card := card_erase_add_one hq
    have e1 := reflect_mul ((C (t q) * (X - C (x q)) + C (u q)) *
        ∏ q' ∈ S.erase q, (X - C (x q')) ^ 2) (1 : K[X])
      ((natDegree_mul_le).trans (add_le_add (natDegree_lin_le x t u q) (natDegree_Pq_le S x q)))
      (show (1 : K[X]).natDegree ≤ 2 by simp)
    rw [mul_one] at e1
    rw [show 2 * S.card + 1 = (1 + (S.erase q).card * 2) + 2 by omega, e1,
      reflect_mul _ _ (natDegree_lin_le x t u q) (natDegree_Pq_le S x q),
      reflect_prod_le (S.erase q) _ 2 (fun q' _ => (natDegree_pow_le).trans
        (by have := natDegree_X_sub_C_le' (R := K) (x q'); omega)),
      reflect_add, reflect_C_mul, reflect_X_sub_C, reflect_C, pow_one,
      show reflect 2 (1 : K[X]) = X ^ 2 by rw [← C_1, reflect_C, C_1, one_mul]]
    congr 2
    exact prod_congr rfl fun q' _ => reflect_sq _

private theorem fP_eq (b₂ b₄ b₆ : K) :
    fP b₂ b₄ b₆ = C 4 * X ^ 3 + C b₂ * X ^ 2 + C (2 * b₄) * X ^ 1 + C b₆ * X ^ 0 := by
  rw [fP, pow_one, pow_zero, mul_one]

private theorem reflect_fP (b₂ b₄ b₆ : K) :
    reflect 3 (fP b₂ b₄ b₆) = C 4 + C b₂ * X + C (2 * b₄) * X ^ 2 + C b₆ * X ^ 3 := by
  rw [fP_eq]
  simp only [reflect_add, reflect_C_mul_X_pow]
  rw [revAt_le (show 3 ≤ 3 by norm_num), revAt_le (show 2 ≤ 3 by norm_num),
    revAt_le (show 1 ≤ 3 by norm_num), revAt_le (show 0 ≤ 3 by norm_num)]
  norm_num

omit [DecidableEq ι] in
private theorem reflect_m (m : ι → K[X]) (b₂ b₄ b₆ b₈ : K)
    (hm : ∀ q ∈ S, m q * (X - C (x q)) = φP b₄ b₆ b₈ - C (d q) * fP b₂ b₄ b₆) :
    ∀ q ∈ S, reflect 3 (m q) * (1 - C (x q) * X)
      = (C 1 * X ^ 0 - C b₄ * X ^ 2 - C (2 * b₆) * X ^ 3 - C b₈ * X ^ 4)
        - C (d q) * (C 4 * X ^ 1 + C b₂ * X ^ 2 + C (2 * b₄) * X ^ 3 + C b₆ * X ^ 4) := by
  intro q hq
  have e := congrArg (reflect 4) (hm q hq)
  rw [show (4 : ℕ) = 3 + 1 from rfl,
    reflect_mul _ _ (natDegree_m_le S x d m b₂ b₄ b₆ b₈ hm q hq) (natDegree_X_sub_C_le' _),
    reflect_X_sub_C] at e
  rw [e, reflect_sub, reflect_C_mul, fP_eq, φP,
    show (X : K[X]) ^ 4 - C b₄ * X ^ 2 - C (2 * b₆) * X - C b₈
      = C 1 * X ^ 4 - C b₄ * X ^ 2 - C (2 * b₆) * X ^ 1 - C b₈ * X ^ 0 by
        rw [C_1, one_mul, pow_one, pow_zero, mul_one]]
  simp only [reflect_add, reflect_sub, reflect_C_mul_X_pow]
  rw [revAt_le (show 4 ≤ 3 + 1 by norm_num), revAt_le (show 2 ≤ 3 + 1 by norm_num),
    revAt_le (show 1 ≤ 3 + 1 by norm_num), revAt_le (show 0 ≤ 3 + 1 by norm_num),
    revAt_le (show 3 ≤ 3 + 1 by norm_num)]

private theorem reflect_diamond (m : ι → K[X]) (b₂ b₄ b₆ b₈ c₂ c₁ c₀ : K)
    (hm : ∀ q ∈ S, m q * (X - C (x q)) = φP b₄ b₆ b₈ - C (d q) * fP b₂ b₄ b₆)
    (hdiamond : C 4 * AP S x t u ^ 3 + C c₂ * AP S x t u ^ 2 * hP S x ^ 2
        + C c₁ * AP S x t u * hP S x ^ 4 + C c₀ * hP S x ^ 6
        = fP b₂ b₄ b₆ * ∏ q ∈ S, m q ^ 2) :
    C 4 * reflect (2 * S.card + 1) (AP S x t u) ^ 3
        + C c₂ * X * reflect (2 * S.card + 1) (AP S x t u) ^ 2 * reflect S.card (hP S x) ^ 2
        + C c₁ * X ^ 2 * reflect (2 * S.card + 1) (AP S x t u) * reflect S.card (hP S x) ^ 4
        + C c₀ * X ^ 3 * reflect S.card (hP S x) ^ 6
      = reflect 3 (fP b₂ b₄ b₆) * ∏ q ∈ S, reflect 3 (m q) ^ 2 := by
  have hdeg_h := natDegree_hP_le S x
  have hdeg_A := natDegree_AP_le S x t u
  have hdeg_f := natDegree_fP_le (K := K) b₂ b₄ b₆
  have hdeg_m := natDegree_m_le S x d m b₂ b₄ b₆ b₈ hm
  set n := S.card with hn
  set h := hP S x with hh
  set A := AP S x t u with hA
  set f := fP b₂ b₄ b₆ with hf
  have hdeg_h2 : (h ^ 2).natDegree ≤ 2 * n :=
    (natDegree_pow_le).trans (Nat.mul_le_mul_left 2 hdeg_h)
  have hdeg_h4 : (h ^ 4).natDegree ≤ 4 * n :=
    (natDegree_pow_le).trans (Nat.mul_le_mul_left 4 hdeg_h)
  have hdeg_h6 : (h ^ 6).natDegree ≤ 6 * n :=
    (natDegree_pow_le).trans (Nat.mul_le_mul_left 6 hdeg_h)
  have hdeg_A2 : (A ^ 2).natDegree ≤ 2 * (2 * n + 1) :=
    (natDegree_pow_le).trans (Nat.mul_le_mul_left 2 hdeg_A)
  have hdeg_A2h2 : (A ^ 2 * h ^ 2).natDegree ≤ 2 * (2 * n + 1) + 2 * n :=
    (natDegree_mul_le).trans (add_le_add hdeg_A2 hdeg_h2)
  have hdeg_Ah4 : (A * h ^ 4).natDegree ≤ (2 * n + 1) + 4 * n :=
    (natDegree_mul_le).trans (add_le_add hdeg_A hdeg_h4)
  have hdeg_m2 : ∀ q ∈ S, (m q ^ 2).natDegree ≤ 6 := fun q hq =>
    (natDegree_pow_le).trans (by have := hdeg_m q hq; omega)
  have hdeg_prod : (∏ q ∈ S, m q ^ 2).natDegree ≤ n * 6 := by
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ i ∈ S, (m i ^ 2).natDegree ≤ ∑ _i ∈ S, 6 := sum_le_sum fun i hi => hdeg_m2 i hi
      _ = n * 6 := by simp [hn]
  have hdegC : ∀ (c : K) (k : ℕ), (C c : K[X]).natDegree ≤ k := fun c k => by simp
  have T3 : reflect (6 * n + 3) (C 4 * A ^ 3) = C 4 * reflect (2 * n + 1) A ^ 3 := by
    rw [reflect_C_mul, show 6 * n + 3 = 3 * (2 * n + 1) by ring, reflect_pow_le A _ 3 hdeg_A]
  have T2 : reflect (6 * n + 3) (C c₂ * A ^ 2 * h ^ 2)
      = C c₂ * X * reflect (2 * n + 1) A ^ 2 * reflect n h ^ 2 := by
    rw [show C c₂ * A ^ 2 * h ^ 2 = (A ^ 2 * h ^ 2) * C c₂ by ring,
      show 6 * n + 3 = (2 * (2 * n + 1) + 2 * n) + 1 by ring,
      reflect_mul _ _ hdeg_A2h2 (hdegC c₂ 1), reflect_mul _ _ hdeg_A2 hdeg_h2,
      reflect_pow_le A _ 2 hdeg_A, reflect_pow_le h _ 2 hdeg_h, reflect_C]
    ring
  have T1 : reflect (6 * n + 3) (C c₁ * A * h ^ 4)
      = C c₁ * X ^ 2 * reflect (2 * n + 1) A * reflect n h ^ 4 := by
    rw [show C c₁ * A * h ^ 4 = (A * h ^ 4) * C c₁ by ring,
      show 6 * n + 3 = ((2 * n + 1) + 4 * n) + 2 by ring,
      reflect_mul _ _ hdeg_Ah4 (hdegC c₁ 2), reflect_mul _ _ hdeg_A hdeg_h4,
      reflect_pow_le h _ 4 hdeg_h, reflect_C]
    ring
  have T0 : reflect (6 * n + 3) (C c₀ * h ^ 6) = C c₀ * X ^ 3 * reflect n h ^ 6 := by
    rw [show C c₀ * h ^ 6 = h ^ 6 * C c₀ by ring,
      reflect_mul _ _ hdeg_h6 (hdegC c₀ 3), reflect_pow_le h _ 6 hdeg_h, reflect_C]
    ring
  have TR : reflect (6 * n + 3) (f * ∏ q ∈ S, m q ^ 2)
      = reflect 3 f * ∏ q ∈ S, reflect 3 (m q) ^ 2 := by
    rw [show 6 * n + 3 = 3 + n * 6 by ring, reflect_mul _ _ hdeg_f hdeg_prod, hn,
      reflect_prod_le S _ 6 hdeg_m2]
    congr 1
    refine prod_congr rfl fun q hq => ?_
    have e := reflect_pow_le (m q) 3 2 (hdeg_m q hq)
    rw [show 2 * 3 = 6 by norm_num] at e
    exact e
  have R := congrArg (reflect (6 * n + 3)) hdiamond
  rw [reflect_add, reflect_add, reflect_add, T3, T2, T1, T0, TR] at R
  exact R

end ReflectAtoms

section Glue

variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → K)

private theorem fiber_to_diamond (ξ₁ ξ₂ ξ₃ : ι → K) (e₁ e₂ e₃ X₁ X₂ X₃ b₂ b₄ b₆ : K)
    (hF₁ : AP S x t u - C X₁ * hP S x ^ 2 = (X - C e₁) * (∏ q ∈ S, (X - C (ξ₁ q))) ^ 2)
    (hF₂ : AP S x t u - C X₂ * hP S x ^ 2 = (X - C e₂) * (∏ q ∈ S, (X - C (ξ₂ q))) ^ 2)
    (hF₃ : AP S x t u - C X₃ * hP S x ^ 2 = (X - C e₃) * (∏ q ∈ S, (X - C (ξ₃ q))) ^ 2)
    (hf : fP b₂ b₄ b₆ = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃))) :
    C 4 * AP S x t u ^ 3 + C (-4 * (X₁ + X₂ + X₃)) * AP S x t u ^ 2 * hP S x ^ 2
        + C (4 * (X₁ * X₂ + X₁ * X₃ + X₂ * X₃)) * AP S x t u * hP S x ^ 4
        + C (-4 * (X₁ * X₂ * X₃)) * hP S x ^ 6
      = fP b₂ b₄ b₆ * ∏ q ∈ S, ((X - C (ξ₁ q)) * (X - C (ξ₂ q)) * (X - C (ξ₃ q))) ^ 2 := by
  have e : C 4 * AP S x t u ^ 3 + C (-4 * (X₁ + X₂ + X₃)) * AP S x t u ^ 2 * hP S x ^ 2
        + C (4 * (X₁ * X₂ + X₁ * X₃ + X₂ * X₃)) * AP S x t u * hP S x ^ 4
        + C (-4 * (X₁ * X₂ * X₃)) * hP S x ^ 6
      = C 4 * ((AP S x t u - C X₁ * hP S x ^ 2) * (AP S x t u - C X₂ * hP S x ^ 2)
          * (AP S x t u - C X₃ * hP S x ^ 2)) := by
    simp only [map_mul, map_neg, map_add]
    ring
  rw [e, hF₁, hF₂, hF₃, hf, prod_pow, prod_mul_distrib, prod_mul_distrib]
  ring

private theorem cubic_eq_of_coeffs (X₁ X₂ X₃ b₂' b₄' b₆' : K) (h₂ : -4 * (X₁ + X₂ + X₃) = b₂')
    (h₁ : 4 * (X₁ * X₂ + X₁ * X₃ + X₂ * X₃) = 2 * b₄') (h₀ : -4 * (X₁ * X₂ * X₃) = b₆') :
    C 4 * ((X - C X₁) * (X - C X₂) * (X - C X₃))
      = C 4 * X ^ 3 + C b₂' * X ^ 2 + C (2 * b₄') * X + C b₆' := by
  rw [← h₂, ← h₁, ← h₀]
  simp only [map_mul, map_neg, map_add]
  ring

omit [DecidableEq ι] in

private theorem roots_cubic (X₁ X₂ X₃ : K) (h4 : (4 : K) ≠ 0) :
    (C 4 * ((X - C X₁) * (X - C X₂) * (X - C X₃))).roots = {X₁, X₂, X₃} := by
  rw [roots_C_mul _ h4, roots_mul (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _)
    (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)), roots_mul (mul_ne_zero (X_sub_C_ne_zero _)
    (X_sub_C_ne_zero _)), roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  rfl

end Glue

section NormBackbone

variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → K)

private noncomputable def SqP (x t u : ι → K) (q : ι) : K[X] :=
  C (2 * x q) * (X - C (x q)) ^ 2 + C (t q) * (X - C (x q)) + C (u q)

private noncomputable def PqP (x : ι → K) (a₂ a₄ a₆ : K) (q : ι) : K[X] :=
  (X * C (x q) - C a₄) ^ 2 - C (4 * a₆) * (X + C (x q) + C a₂)

private noncomputable def MM (a₂ a₄ a₆ : K) : K[X][X] :=
  (X - C X) * ∏ q ∈ S, ((C : K[X] →+* K[X][X]) ((X - C (x q)) ^ 2) * X ^ 2
    - (C : K[X] →+* K[X][X]) (SqP x t u q) * X + (C : K[X] →+* K[X][X]) (PqP x a₂ a₄ a₆ q))

private noncomputable def PP : K[X][X] :=
  (C : K[X] →+* K[X][X]) (hP S x ^ 2) * (AP S x t u).map C
    - (C : K[X] →+* K[X][X]) (AP S x t u) * ((hP S x).map C) ^ 2

omit [DecidableEq ι] in
private theorem hP_monic : (hP S x).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

omit [DecidableEq ι] in
private theorem natDegree_hP : (hP S x).natDegree = S.card := by
  rw [hP, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

private theorem natDegree_AP_sum_le :
    (∑ q ∈ S, (C (t q) * (X - C (x q)) + C (u q)) * ∏ q' ∈ S.erase q, (X - C (x q')) ^ 2
      : K[X]).natDegree ≤ 2 * S.card - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun q hq => ?_
  refine (natDegree_mul_le).trans ?_
  have h1 := natDegree_lin_le x t u q
  have h2 := natDegree_Pq_le S x q
  have h3 : (S.erase q).card + 1 = S.card := card_erase_add_one hq
  omega

private theorem degree_AP_sum_lt :
    (∑ q ∈ S, (C (t q) * (X - C (x q)) + C (u q)) * ∏ q' ∈ S.erase q, (X - C (x q')) ^ 2
      : K[X]).degree < (X * hP S x ^ 2).degree := by
  refine lt_of_le_of_lt (degree_le_of_natDegree_le (natDegree_AP_sum_le S x t u)) ?_
  rw [degree_eq_natDegree (monic_X.mul ((hP_monic S x).pow 2)).ne_zero,
    natDegree_X_mul ((hP_monic S x).pow 2).ne_zero, (hP_monic S x).natDegree_pow, natDegree_hP]
  exact_mod_cast (show 2 * S.card - 1 < 2 * S.card + 1 by omega)

private theorem AP_monic : (AP S x t u).Monic := by
  rw [AP]
  exact Monic.add_of_left (monic_X.mul ((hP_monic S x).pow 2)) (degree_AP_sum_lt S x t u)

private theorem natDegree_AP : (AP S x t u).natDegree = 2 * S.card + 1 := by
  rw [AP, natDegree_add_eq_left_of_degree_lt (degree_AP_sum_lt S x t u),
    natDegree_X_mul ((hP_monic S x).pow 2).ne_zero, (hP_monic S x).natDegree_pow, natDegree_hP]

private noncomputable abbrev spec (x₀ : K) : K[X][X] →+* K[X] := mapRingHom (evalRingHom x₀)

omit [DecidableEq ι] in
private theorem spec_C (x₀ : K) (p : K[X]) : spec x₀ ((C : K[X] →+* K[X][X]) p) = C (p.eval x₀) := by
  simp [spec]

omit [DecidableEq ι] in
private theorem spec_map_C (x₀ : K) (p : K[X]) : spec x₀ (p.map C) = p := by
  rw [spec, coe_mapRingHom, Polynomial.map_map]
  have : (evalRingHom x₀).comp C = RingHom.id K := RingHom.ext fun a => eval_C
  rw [this, Polynomial.map_id]

omit [DecidableEq ι] in
private theorem spec_X (x₀ : K) : spec x₀ (X : K[X][X]) = X := by
  simp [spec]

private theorem spec_PP (x₀ : K) : spec x₀ (PP S x t u)
    = C ((hP S x).eval x₀ ^ 2) * AP S x t u - C ((AP S x t u).eval x₀) * hP S x ^ 2 := by
  simp only [PP, map_sub, map_mul, map_pow, spec_C, spec_map_C]

omit [DecidableEq ι] in
private theorem spec_MM (x₀ a₂ a₄ a₆ : K) : spec x₀ (MM S x t u a₂ a₄ a₆)
    = (X - C x₀) * ∏ q ∈ S, (C ((x₀ - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval x₀) * X
        + C ((PqP x a₂ a₄ a₆ q).eval x₀)) := by
  simp only [MM, map_mul, map_sub, map_add, map_prod, map_pow, spec_X, spec_C, eval_X, eval_C]

private theorem MM_eq_PP_of_infinite (a₂ a₄ a₆ : K)
    (hinf : Set.Infinite {x₀ : K | spec x₀ (MM S x t u a₂ a₄ a₆) = spec x₀ (PP S x t u)}) :
    MM S x t u a₂ a₄ a₆ = PP S x t u := by
  rw [← sub_eq_zero]
  refine Polynomial.ext fun i => ?_
  rw [coeff_zero]
  refine eq_zero_of_infinite_isRoot _ (hinf.mono fun x₀ hx₀ => ?_)
  simp only [Set.mem_setOf_eq] at hx₀ ⊢
  have e := congrArg (fun p : K[X] => p.coeff i) hx₀
  simp only [spec, coe_mapRingHom, coeff_map, coe_evalRingHom] at e
  rw [IsRoot.def, coeff_sub, eval_sub, e, sub_self]

private theorem fiber_of_MM_eq_PP (a₂ a₄ a₆ : K) (hMP : MM S x t u a₂ a₄ a₆ = PP S x t u) (e : K)
    (ξ : ι → K) (hfac : ∀ q ∈ S, C ((e - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval e) * X
        + C ((PqP x a₂ a₄ a₆ q).eval e) = C ((e - x q) ^ 2) * (X - C (ξ q)) ^ 2)
    (he : (hP S x).eval e ≠ 0) :
    AP S x t u - C ((AP S x t u).eval e / (hP S x).eval e ^ 2) * hP S x ^ 2
      = (X - C e) * (∏ q ∈ S, (X - C (ξ q))) ^ 2 := by
  have key := congrArg (spec e) hMP
  rw [spec_MM, spec_PP, prod_congr rfl hfac, prod_mul_distrib, prod_pow, ← map_prod,
    show ∏ q ∈ S, (e - x q) ^ 2 = (hP S x).eval e ^ 2 by
      rw [hP, eval_prod, ← prod_pow]; simp [eval_sub, eval_X, eval_C]] at key
  have he2 : C ((hP S x).eval e ^ 2) ≠ 0 := by
    rw [Ne, C_eq_zero]; exact pow_ne_zero 2 he
  refine mul_left_cancel₀ he2 ?_
  rw [mul_sub, ← mul_assoc, ← map_mul, show (hP S x).eval e ^ 2 * ((AP S x t u).eval e
      / (hP S x).eval e ^ 2) = (AP S x t u).eval e by field_simp, ← key]
  ring

omit [DecidableEq ι] in

private theorem chord_factor (x₁ x₂ tq uq a₂ a₄ a₆ τp τm : K) (hx : x₁ ≠ x₂)
    (hsum : τp + τm = 2 * x₂ + tq / (x₁ - x₂) + uq / (x₁ - x₂) ^ 2)
    (hprod : τp * τm = ((x₁ * x₂ - a₄) ^ 2 - 4 * a₆ * (x₁ + x₂ + a₂)) / (x₁ - x₂) ^ 2) :
    C ((x₁ - x₂) ^ 2) * X ^ 2 - C (2 * x₂ * (x₁ - x₂) ^ 2 + tq * (x₁ - x₂) + uq) * X
        + C ((x₁ * x₂ - a₄) ^ 2 - 4 * a₆ * (x₁ + x₂ + a₂))
      = C ((x₁ - x₂) ^ 2) * (X - C τp) * (X - C τm) := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hs : 2 * x₂ * (x₁ - x₂) ^ 2 + tq * (x₁ - x₂) + uq = (x₁ - x₂) ^ 2 * (τp + τm) := by
    rw [hsum]; field_simp
  have hp : (x₁ * x₂ - a₄) ^ 2 - 4 * a₆ * (x₁ + x₂ + a₂) = (x₁ - x₂) ^ 2 * (τp * τm) := by
    rw [hprod]; field_simp
  rw [hs, hp]
  simp only [map_mul, map_add, map_pow, map_sub]
  ring

omit [DecidableEq ι] in

private theorem eval_SqP (x t u : ι → K) (q : ι) (x₀ : K) :
    (SqP x t u q).eval x₀ = 2 * x q * (x₀ - x q) ^ 2 + t q * (x₀ - x q) + u q := by
  simp [SqP]

omit [DecidableEq ι] in
private theorem eval_PqP (x : ι → K) (a₂ a₄ a₆ : K) (q : ι) (x₀ : K) :
    (PqP x a₂ a₄ a₆ q).eval x₀ = (x₀ * x q - a₄) ^ 2 - 4 * a₆ * (x₀ + x q + a₂) := by
  simp only [PqP, eval_sub, eval_pow, eval_mul, eval_add, eval_X, eval_C]

end NormBackbone

section CurveFacing

variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → K)

private noncomputable def Xv (v : K) : K := v + ∑ q ∈ S, (t q / (v - x q) + u q / (v - x q) ^ 2)

omit [DecidableEq ι] in
private theorem hP_eval (v : K) : (hP S x).eval v = ∏ q ∈ S, (v - x q) := by
  rw [hP, eval_prod]
  simp

omit [DecidableEq ι] in
private theorem hP_eval_ne_zero (v : K) (hv : ∀ q ∈ S, v ≠ x q) : (hP S x).eval v ≠ 0 := by
  rw [hP_eval]
  exact prod_ne_zero_iff.mpr fun q hq => sub_ne_zero.mpr (hv q hq)

private theorem AP_eval (v : K) (hv : ∀ q ∈ S, v ≠ x q) :
    (AP S x t u).eval v = (hP S x).eval v ^ 2 * Xv S x t u v := by
  have hh : ∀ q ∈ S, (hP S x).eval v = (v - x q) * ∏ q' ∈ S.erase q, (v - x q') := by
    intro q hq
    rw [hP_eval, mul_prod_erase S (fun q' => v - x q') hq]
  rw [AP, Xv]
  simp only [eval_add, eval_mul, eval_X, eval_pow, eval_finsetSum, eval_prod, eval_sub, eval_C]
  rw [mul_add, mul_sum, mul_comm]
  congr 1
  refine sum_congr rfl fun q hq => ?_
  have hvq : v - x q ≠ 0 := sub_ne_zero.mpr (hv q hq)
  rw [hh q hq, prod_pow]
  field_simp

private theorem norm_identity' (x₀ c : K) (τp τm : ι → K)
    (h0p : ∀ q ∈ S, x₀ ≠ τp q) (h0m : ∀ q ∈ S, x₀ ≠ τm q)
    (hpp : Set.InjOn τp S) (hmm : Set.InjOn τm S) (hpm : ∀ q ∈ S, ∀ q' ∈ S, τp q ≠ τm q')
    (hr0 : (AP S x t u).eval x₀ = c * (hP S x).eval x₀ ^ 2)
    (hrp : ∀ q ∈ S, (AP S x t u).eval (τp q) = c * (hP S x).eval (τp q) ^ 2)
    (hrm : ∀ q ∈ S, (AP S x t u).eval (τm q) = c * (hP S x).eval (τm q) ^ 2) :
    (X - C x₀) * ∏ q ∈ S, ((X - C (τp q)) * (X - C (τm q))) = AP S x t u - C c * hP S x ^ 2 := by
  classical

  set s : Finset K := insert x₀ (S.image τp ∪ S.image τm) with hs
  have hdisj : Disjoint (S.image τp) (S.image τm) := by
    rw [disjoint_iff_ne]
    rintro a ha b hb rfl
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ha
    obtain ⟨q', hq', e⟩ := mem_image.mp hb
    exact hpm q hq q' hq' e.symm
  have hx₀ : x₀ ∉ S.image τp ∪ S.image τm := by
    intro hmem
    rcases mem_union.mp hmem with h | h
    · obtain ⟨q, hq, e⟩ := mem_image.mp h; exact h0p q hq e.symm
    · obtain ⟨q, hq, e⟩ := mem_image.mp h; exact h0m q hq e.symm
  have hcard : s.card = 2 * S.card + 1 := by
    rw [hs, card_insert_of_notMem hx₀, card_union_of_disjoint hdisj, card_image_of_injOn hpp,
      card_image_of_injOn hmm]
    ring

  set M := (X - C x₀) * ∏ q ∈ S, ((X - C (τp q)) * (X - C (τm q))) with hM
  have hMmon : M.Monic := (monic_X_sub_C _).mul (monic_prod_of_monic _ _ fun q _ =>
    (monic_X_sub_C _).mul (monic_X_sub_C _))
  have hMdeg : M.natDegree = 2 * S.card + 1 := by
    rw [hM, (monic_X_sub_C _).natDegree_mul (monic_prod_of_monic _ _ fun q _ =>
      (monic_X_sub_C _).mul (monic_X_sub_C _)), natDegree_X_sub_C,
      natDegree_prod_of_monic _ _ fun q _ => (monic_X_sub_C _).mul (monic_X_sub_C _)]
    rw [sum_congr rfl fun q _ => (monic_X_sub_C (τp q)).natDegree_mul (monic_X_sub_C (τm q))]
    simp only [natDegree_X_sub_C, sum_const, smul_eq_mul]
    ring
  have hA := AP_monic S x t u
  have hAdeg := natDegree_AP S x t u
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq s ?_ ?_
  · have e : M - (AP S x t u - C c * hP S x ^ 2) = (M - AP S x t u) + C c * hP S x ^ 2 := by ring
    rw [e, hcard]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · by_cases h0 : M - AP S x t u = 0
      · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
      have := degree_sub_lt (p := M) (q := AP S x t u)
        (by rw [degree_eq_natDegree hMmon.ne_zero, degree_eq_natDegree hA.ne_zero, hMdeg, hAdeg])
        hMmon.ne_zero (by rw [hMmon.leadingCoeff, hA.leadingCoeff])
      rwa [degree_eq_natDegree hMmon.ne_zero, hMdeg] at this
    · refine lt_of_le_of_lt (degree_le_of_natDegree_le ((natDegree_C_mul_le _ _).trans
        ((natDegree_pow_le).trans (Nat.mul_le_mul_left 2 (natDegree_hP_le S x))))) ?_
      exact_mod_cast (show 2 * S.card < 2 * S.card + 1 by omega)
  · intro v hv
    have hR : ∀ w, (AP S x t u).eval w = c * (hP S x).eval w ^ 2 →
        (AP S x t u - C c * hP S x ^ 2).eval w = 0 := fun w hw => by
      rw [eval_sub, eval_mul, eval_C, eval_pow, hw, sub_self]
    rw [hs, mem_insert, mem_union, mem_image, mem_image] at hv
    rcases hv with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · rw [hR _ hr0, hM, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
    · rw [hR _ (hrp q hq), hM, eval_mul, eval_prod, prod_eq_zero hq (by simp), mul_zero]
    · rw [hR _ (hrm q hq), hM, eval_mul, eval_prod, prod_eq_zero hq (by simp), mul_zero]

private theorem spec_MM_eq_spec_PP_at (a₂ a₄ a₆ x₀ c : K) (τp τm : ι → K)
    (hx : ∀ q ∈ S, x₀ ≠ x q)
    (hsum : ∀ q ∈ S, τp q + τm q = 2 * x q + t q / (x₀ - x q) + u q / (x₀ - x q) ^ 2)
    (hprod : ∀ q ∈ S, τp q * τm q
      = ((x₀ * x q - a₄) ^ 2 - 4 * a₆ * (x₀ + x q + a₂)) / (x₀ - x q) ^ 2)
    (hnorm : (X - C x₀) * ∏ q ∈ S, ((X - C (τp q)) * (X - C (τm q)))
      = AP S x t u - C c * hP S x ^ 2)
    (hc : c * (hP S x).eval x₀ ^ 2 = (AP S x t u).eval x₀) :
    spec x₀ (MM S x t u a₂ a₄ a₆) = spec x₀ (PP S x t u) := by
  rw [spec_MM, spec_PP]
  have e1 : ∀ q ∈ S, C ((x₀ - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval x₀) * X
      + C ((PqP x a₂ a₄ a₆ q).eval x₀) = C ((x₀ - x q) ^ 2) * ((X - C (τp q)) * (X - C (τm q))) := by
    intro q hq
    rw [eval_SqP, eval_PqP, chord_factor (x₀) (x q) (t q) (u q) a₂ a₄ a₆ (τp q) (τm q) (hx q hq)
      (hsum q hq) (hprod q hq), mul_assoc]
  rw [prod_congr rfl e1, prod_mul_distrib, ← map_prod,
    show ∏ q ∈ S, (x₀ - x q) ^ 2 = (hP S x).eval x₀ ^ 2 by rw [hP_eval, prod_pow],
    mul_left_comm, hnorm, ← hc, map_mul]
  ring

end CurveFacing

private theorem expansion {ι : Type*} [DecidableEq ι] (S : Finset ι) (x d t u : ι → K)
    (m : ι → K[X]) (b₂ b₄ b₆ b₈ c₂ c₁ c₀ : K)
    (ht : ∀ q ∈ S, t q = 6 * x q ^ 2 + b₂ * x q + b₄)
    (hu : ∀ q ∈ S, u q = 4 * x q ^ 3 + b₂ * x q ^ 2 + 2 * b₄ * x q + b₆)
    (hperm : S.val.map d = S.val.map x)
    (hm : ∀ q ∈ S, m q * (X - C (x q)) = φP b₄ b₆ b₈ - C (d q) * fP b₂ b₄ b₆)
    (hdiamond : C 4 * AP S x t u ^ 3 + C c₂ * AP S x t u ^ 2 * hP S x ^ 2
        + C c₁ * AP S x t u * hP S x ^ 4 + C c₀ * hP S x ^ 6
        = fP b₂ b₄ b₆ * ∏ q ∈ S, m q ^ 2) :
    c₂ = b₂ ∧ c₁ = 2 * b₄ - 20 * ∑ q ∈ S, t q
      ∧ c₀ = b₆ - 4 * b₂ * (∑ q ∈ S, t q) - 28 * ∑ q ∈ S, (u q + x q * t q) := by
  exact expansion_core S x d t u b₂ b₄ b₆ b₈ c₂ c₁ c₀ ht hu hperm _ _ _ _
    (reflect_hP S x) (reflect_AP S x t u) (reflect_fP b₂ b₄ b₆) (reflect_m S x d m b₂ b₄ b₆ b₈ hm)
    (reflect_diamond S x d t u m b₂ b₄ b₆ b₈ c₂ c₁ c₀ hm hdiamond)

section DeltaAlgebra

variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → K)

private theorem delta_identity (ξ₁ ξ₂ : ι → K) (e₁ e₂ e₃ X₁ X₂ X₃ Δ Δ' : K)
    (hA₂ : (AP S x t u).eval e₂ = (hP S x).eval e₂ ^ 2 * X₂)
    (hA₃ : (AP S x t u).eval e₃ = (hP S x).eval e₃ ^ 2 * X₃)
    (hF₁₂ : (AP S x t u).eval e₂ - X₁ * (hP S x).eval e₂ ^ 2
      = (e₂ - e₁) * (∏ q ∈ S, (e₂ - ξ₁ q)) ^ 2)
    (hF₁₃ : (AP S x t u).eval e₃ - X₁ * (hP S x).eval e₃ ^ 2
      = (e₃ - e₁) * (∏ q ∈ S, (e₃ - ξ₁ q)) ^ 2)
    (hF₂₃ : (AP S x t u).eval e₃ - X₂ * (hP S x).eval e₃ ^ 2
      = (e₃ - e₂) * (∏ q ∈ S, (e₃ - ξ₂ q)) ^ 2)
    (hL₁₂ : ∀ q ∈ S, (e₂ - ξ₁ q) * (x q - e₁) = -((e₁ - e₂) * (x q - e₃)))
    (hL₁₃ : ∀ q ∈ S, (e₃ - ξ₁ q) * (x q - e₁) = -((e₁ - e₃) * (x q - e₂)))
    (hL₂₃ : ∀ q ∈ S, (e₃ - ξ₂ q) * (x q - e₂) = -((e₂ - e₃) * (x q - e₁)))
    (he₁ : ∀ q ∈ S, e₁ ≠ x q) (he₂ : ∀ q ∈ S, e₂ ≠ x q) (he₃ : ∀ q ∈ S, e₃ ≠ x q)
    (hu : ∀ q ∈ S, u q = 4 * ((x q - e₁) * (x q - e₂) * (x q - e₃)))
    (hΔ : Δ = 16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2)
    (hΔ' : Δ' = 16 * ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2) :
    Δ' * (∏ q ∈ S, u q) ^ 4 = Δ ^ (2 * S.card + 1) := by
  set n := S.card with hn
  set H₁ := ∏ q ∈ S, (x q - e₁) with hH₁
  set H₂ := ∏ q ∈ S, (x q - e₂) with hH₂
  set H₃ := ∏ q ∈ S, (x q - e₃) with hH₃
  have hH₁0 : H₁ ≠ 0 := prod_ne_zero_iff.mpr fun q hq => sub_ne_zero.mpr (he₁ q hq).symm
  have hH₂0 : H₂ ≠ 0 := prod_ne_zero_iff.mpr fun q hq => sub_ne_zero.mpr (he₂ q hq).symm
  have hH₃0 : H₃ ≠ 0 := prod_ne_zero_iff.mpr fun q hq => sub_ne_zero.mpr (he₃ q hq).symm

  have hsq : ∀ e : K, (hP S x).eval e ^ 2 = (∏ q ∈ S, (x q - e)) ^ 2 := fun e => by
    rw [hP_eval, ← prod_pow, ← prod_pow]
    exact prod_congr rfl fun q _ => by ring

  have hG : ∀ (ξ : ι → K) (ej ek el : K),
      (∀ q ∈ S, (ek - ξ q) * (x q - ej) = -((ej - ek) * (x q - el))) →
      (∏ q ∈ S, (ek - ξ q)) * (∏ q ∈ S, (x q - ej)) = (ek - ej) ^ n * ∏ q ∈ S, (x q - el) := by
    intro ξ ej ek el hL
    rw [← prod_mul_distrib, prod_congr rfl fun q hq => (hL q hq).trans
      (show -((ej - ek) * (x q - el)) = (ek - ej) * (x q - el) by ring), prod_mul_distrib,
      prod_const, hn]
  have G₁₂ := hG ξ₁ e₁ e₂ e₃ hL₁₂
  have G₁₃ := hG ξ₁ e₁ e₃ e₂ hL₁₃
  have G₂₃ := hG ξ₂ e₂ e₃ e₁ hL₂₃
  simp only [← hH₁, ← hH₂, ← hH₃] at G₁₂ G₁₃ G₂₃
  simp only [hsq] at hA₂ hA₃ hF₁₂ hF₁₃ hF₂₃
  simp only [← hH₂, ← hH₃] at hA₂ hA₃ hF₁₂ hF₁₃ hF₂₃

  have pair : ∀ (G Hj Hk Hl Xj Xk ej ek Ae : K),
      Ae = Hk ^ 2 * Xk → Ae - Xj * Hk ^ 2 = (ek - ej) * G ^ 2 → G * Hj = (ek - ej) ^ n * Hl →
      (Xj - Xk) ^ 2 * Hj ^ 4 * Hk ^ 4 = (ek - ej) ^ (2 * (2 * n + 1)) * Hl ^ 4 := by
    intro G Hj Hk Hl Xj Xk ej ek Ae hA hF hGH
    have e1 : (Xk - Xj) * Hk ^ 2 * Hj ^ 2 = (ek - ej) * (G * Hj) ^ 2 := by
      linear_combination Hj ^ 2 * (hF - hA)
    rw [hGH] at e1
    calc (Xj - Xk) ^ 2 * Hj ^ 4 * Hk ^ 4 = ((Xk - Xj) * Hk ^ 2 * Hj ^ 2) ^ 2 := by ring
      _ = ((ek - ej) * ((ek - ej) ^ n * Hl) ^ 2) ^ 2 := by rw [e1]
      _ = (ek - ej) ^ (2 * (2 * n + 1)) * Hl ^ 4 := by ring
  have P₁₂ := pair _ H₁ H₂ H₃ X₁ X₂ e₁ e₂ _ hA₂ hF₁₂ G₁₂
  have P₁₃ := pair _ H₁ H₃ H₂ X₁ X₃ e₁ e₃ _ hA₃ hF₁₃ G₁₃
  have P₂₃ := pair _ H₂ H₃ H₁ X₂ X₃ e₂ e₃ _ hA₃ hF₂₃ G₂₃
  have hΔ2 : Δ = 16 * ((e₂ - e₁) * (e₃ - e₁) * (e₃ - e₂)) ^ 2 := by rw [hΔ]; ring

  have hU : ∏ q ∈ S, u q = 4 ^ n * (H₁ * H₂ * H₃) := by
    rw [prod_congr rfl hu, prod_mul_distrib, prod_const, prod_mul_distrib, prod_mul_distrib, hn]
  have h16 : (16 : K) ^ (2 * n + 1) = 16 * ((4 : K) ^ n) ^ 4 := by
    rw [pow_succ, pow_mul, ← pow_mul (4 : K) n 4, mul_comm n 4, pow_mul,
      show ((16 : K)) ^ 2 = 4 ^ 4 by norm_num]
    ring
  clear_value H₁ H₂ H₃
  generalize e₂ - e₁ = a at P₁₂ hΔ2
  generalize e₃ - e₁ = b at P₁₃ hΔ2
  generalize e₃ - e₂ = c at P₂₃ hΔ2

  have hP0 : (H₁ * H₂ * H₃) ^ 4 ≠ 0 := pow_ne_zero 4 (mul_ne_zero (mul_ne_zero hH₁0 hH₂0) hH₃0)
  have key : ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 * (H₁ * H₂ * H₃) ^ 4 * (H₁ * H₂ * H₃) ^ 4
      = a ^ (2 * (2 * n + 1)) * b ^ (2 * (2 * n + 1)) * c ^ (2 * (2 * n + 1))
        * (H₁ * H₂ * H₃) ^ 4 := by
    have e3 : ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 * (H₁ * H₂ * H₃) ^ 4 * (H₁ * H₂ * H₃) ^ 4
        = ((X₁ - X₂) ^ 2 * H₁ ^ 4 * H₂ ^ 4) * ((X₁ - X₃) ^ 2 * H₁ ^ 4 * H₃ ^ 4)
          * ((X₂ - X₃) ^ 2 * H₂ ^ 4 * H₃ ^ 4) := by ring
    rw [e3, P₁₂, P₁₃, P₂₃]
    ring
  have key2 : ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 * (H₁ * H₂ * H₃) ^ 4
      = a ^ (2 * (2 * n + 1)) * b ^ (2 * (2 * n + 1)) * c ^ (2 * (2 * n + 1)) :=
    mul_right_cancel₀ hP0 key
  calc Δ' * (∏ q ∈ S, u q) ^ 4
      = 16 * (4 ^ n) ^ 4 * (((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 * (H₁ * H₂ * H₃) ^ 4) := by
        rw [hΔ', hU]; ring
    _ = 16 * (4 ^ n) ^ 4 * (a ^ (2 * (2 * n + 1)) * b ^ (2 * (2 * n + 1))
        * c ^ (2 * (2 * n + 1))) := by rw [key2]
    _ = Δ ^ (2 * n + 1) := by rw [hΔ2, mul_pow, h16]; ring

end DeltaAlgebra

private theorem fiber {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → K) (a₂ a₄ a₆ : K)
    (hMP : MM S x t u a₂ a₄ a₆ = PP S x t u) (e : K) (ξ : ι → K) (he : ∀ q ∈ S, e ≠ x q)
    (hfac : ∀ q ∈ S, C ((e - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval e) * X
        + C ((PqP x a₂ a₄ a₆ q).eval e) = C ((e - x q) ^ 2) * (X - C (ξ q)) ^ 2) :
    AP S x t u - C (Xv S x t u e) * hP S x ^ 2 = (X - C e) * (∏ q ∈ S, (X - C (ξ q))) ^ 2 := by
  have hh := hP_eval_ne_zero S x e he
  have key := fiber_of_MM_eq_PP S x t u a₂ a₄ a₆ hMP e ξ hfac hh
  rwa [AP_eval S x t u e he, mul_div_cancel_left₀ _ (pow_ne_zero 2 hh)] at key

private theorem pipeline {ι : Type*} [DecidableEq ι] (S : Finset ι) (x d t u : ι → K)
    (ξ₁ ξ₂ ξ₃ : ι → K) (a₂ a₄ a₆ e₁ e₂ e₃ : K)
    (hMP : MM S x t u a₂ a₄ a₆ = PP S x t u)
    (he₁ : ∀ q ∈ S, e₁ ≠ x q) (he₂ : ∀ q ∈ S, e₂ ≠ x q) (he₃ : ∀ q ∈ S, e₃ ≠ x q)
    (hfac₁ : ∀ q ∈ S, C ((e₁ - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval e₁) * X
        + C ((PqP x a₂ a₄ a₆ q).eval e₁) = C ((e₁ - x q) ^ 2) * (X - C (ξ₁ q)) ^ 2)
    (hfac₂ : ∀ q ∈ S, C ((e₂ - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval e₂) * X
        + C ((PqP x a₂ a₄ a₆ q).eval e₂) = C ((e₂ - x q) ^ 2) * (X - C (ξ₂ q)) ^ 2)
    (hfac₃ : ∀ q ∈ S, C ((e₃ - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval e₃) * X
        + C ((PqP x a₂ a₄ a₆ q).eval e₃) = C ((e₃ - x q) ^ 2) * (X - C (ξ₃ q)) ^ 2)
    (hvieta : fP (4 * a₂) (2 * a₄) (4 * a₆) = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))
    (ht : ∀ q ∈ S, t q = 6 * x q ^ 2 + 4 * a₂ * x q + 2 * a₄)
    (hu : ∀ q ∈ S, u q = 4 * x q ^ 3 + 4 * a₂ * x q ^ 2 + 2 * (2 * a₄) * x q + 4 * a₆)
    (hperm : S.val.map d = S.val.map x)
    (hpack : ∀ q ∈ S, (X - C (ξ₁ q)) * (X - C (ξ₂ q)) * (X - C (ξ₃ q)) * (X - C (x q))
        = φP (2 * a₄) (4 * a₆) (4 * a₂ * a₆ - a₄ ^ 2) - C (d q) * fP (4 * a₂) (2 * a₄) (4 * a₆)) :
    C 4 * ((X - C (Xv S x t u e₁)) * (X - C (Xv S x t u e₂)) * (X - C (Xv S x t u e₃)))
      = C 4 * X ^ 3 + C (4 * a₂) * X ^ 2 + C (2 * (2 * a₄ - 10 * ∑ q ∈ S, t q)) * X
        + C (4 * a₆ - 4 * (4 * a₂) * (∑ q ∈ S, t q) - 28 * ∑ q ∈ S, (u q + x q * t q)) := by

  have F := fiber S x t u a₂ a₄ a₆ hMP
  have D := fiber_to_diamond S x t u ξ₁ ξ₂ ξ₃ e₁ e₂ e₃ (Xv S x t u e₁) (Xv S x t u e₂)
    (Xv S x t u e₃) (4 * a₂) (2 * a₄) (4 * a₆) (F e₁ ξ₁ he₁ hfac₁) (F e₂ ξ₂ he₂ hfac₂)
    (F e₃ ξ₃ he₃ hfac₃) hvieta
  obtain ⟨k₂, k₁, k₀⟩ := expansion S x d t u (fun q => (X - C (ξ₁ q)) * (X - C (ξ₂ q))
    * (X - C (ξ₃ q))) (4 * a₂) (2 * a₄) (4 * a₆) (4 * a₂ * a₆ - a₄ ^ 2) _ _ _ ht hu hperm hpack D
  exact cubic_eq_of_coeffs _ _ _ _ _ _ k₂ (by rw [k₁]; ring) k₀

section Curve

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

variable {F : Type*} [Field F] [DecidableEq F]

variable {V : WeierstrassCurve F}

private theorem two_torsion_chord_factor (ha1 : V.a₁ = 0) (ha3 : V.a₃ = 0) {e xq yq : F}
    (he : V.toAffine.Equation e 0) (hq : V.toAffine.Equation xq yq) (hex : e ≠ xq) :
    C ((e - xq) ^ 2) * X ^ 2 - C (2 * xq * (e - xq) ^ 2 + V.veluT xq yq * (e - xq)
        + V.veluU xq yq) * X + C ((e * xq - V.a₄) ^ 2 - 4 * V.a₆ * (e + xq + V.a₂))
      = C ((e - xq) ^ 2) * (X - C (V.toAffine.addX e xq (V.toAffine.slope e xq 0 yq))) ^ 2 := by
  have hsum := N5IDAux4.chord_sum' V he hq hex
  have hprod := N5IDAux4.chord_prod V ha1 ha3 he hq hex
  have hτ : V.toAffine.addX e xq (V.toAffine.slope e xq 0 (V.toAffine.negY xq yq))
      = V.toAffine.addX e xq (V.toAffine.slope e xq 0 yq) := by
    rw [Affine.slope_of_X_ne hex, Affine.slope_of_X_ne hex]
    simp only [Affine.addX, Affine.negY, toAffine, ha1, ha3]
    ring
  rw [hτ] at hsum hprod
  rw [pow_two (X - C _), ← mul_assoc]
  exact chord_factor e xq _ _ V.a₂ V.a₄ V.a₆ _ _ hex hsum hprod

private def xco (P : V.toAffine.Point) : F := P.coordsOrZero.1

omit [DecidableEq F] in
private theorem eq_or_eq_neg_of_xco_eq {P P' : V.toAffine.Point} (hP : P ≠ 0) (hP' : P' ≠ 0)
    (h : xco P = xco P') : P = P' ∨ P = -P' := by
  rcases P with _ | ⟨a, b, hab⟩
  · exact absurd rfl hP
  rcases P' with _ | ⟨a', b', hab'⟩
  · exact absurd rfl hP'
  exact (Affine.Point.X_eq_iff (h₁ := hab) (h₂ := hab')).mp h

variable {Q z : V.toAffine.Point} {n : ℕ}

private theorem good_add_nsmul_ne_zero (hz : ∀ j : ℕ, 2 • z + j • Q ≠ 0) (j : ℕ) : z + j • Q ≠ 0 := by
  intro h
  apply hz (2 * j)
  rw [mul_nsmul', ← nsmul_add, h, nsmul_zero]

private theorem good_xco_ne (hQ : addOrderOf Q = 2 * n + 1) (hz : ∀ j : ℕ, 2 • z + j • Q ≠ 0)
    {j₁ j₂ : ℕ} (hlt : j₁ < j₂) (hlt' : j₂ < j₁ + (2 * n + 1)) :
    xco (z + j₁ • Q) ≠ xco (z + j₂ • Q) := by
  intro h
  rcases eq_or_eq_neg_of_xco_eq (good_add_nsmul_ne_zero hz j₁) (good_add_nsmul_ne_zero hz j₂) h
    with e | e
  · have h0 : (j₂ - j₁) • Q = 0 := by
      have e2 : z + j₁ • Q + (j₂ - j₁) • Q = z + j₁ • Q + 0 := by
        rw [add_zero, add_assoc, ← add_nsmul, Nat.add_sub_cancel' hlt.le, ← e]
      exact add_left_cancel e2
    have hdvd : 2 * n + 1 ∣ j₂ - j₁ := hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · apply hz (j₁ + j₂)
    have e2 : z + j₁ • Q + (z + j₂ • Q) = 0 := by rw [e, neg_add_cancel]
    rw [two_nsmul, add_nsmul, ← e2]
    abel

private theorem good_xco_ne_kernel (hQ : addOrderOf Q = 2 * n + 1) (hz : ∀ j : ℕ, 2 • z + j • Q ≠ 0)
    (j k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 2 * n) : xco (z + j • Q) ≠ xco (k • Q) := by
  intro h
  have hk0 : k • Q ≠ 0 := fun h0 => by
    have hdvd : 2 * n + 1 ∣ k := hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  rcases eq_or_eq_neg_of_xco_eq (good_add_nsmul_ne_zero hz j) hk0 h with e | e
  · apply good_add_nsmul_ne_zero hz (j + (2 * n + 1 - k))
    rw [add_nsmul, ← add_assoc, e, ← add_nsmul, Nat.add_sub_cancel' (by omega : k ≤ 2 * n + 1),
      ← hQ, addOrderOf_nsmul_eq_zero]
  · apply good_add_nsmul_ne_zero hz (j + k)
    rw [add_nsmul, ← add_assoc, e, neg_add_cancel]

private theorem good_distinct (hQ : addOrderOf Q = 2 * n + 1) (hz : ∀ j : ℕ, 2 • z + j • Q ≠ 0) :
    (∀ k ∈ Finset.Icc 1 n, xco z ≠ xco (z + k • Q))
    ∧ (∀ k ∈ Finset.Icc 1 n, xco z ≠ xco (z + (2 * n + 1 - k) • Q))
    ∧ Set.InjOn (fun k => xco (z + k • Q)) (↑(Finset.Icc 1 n) : Set ℕ)
    ∧ Set.InjOn (fun k => xco (z + (2 * n + 1 - k) • Q)) (↑(Finset.Icc 1 n) : Set ℕ)
    ∧ (∀ k ∈ Finset.Icc 1 n, ∀ k' ∈ Finset.Icc 1 n,
        xco (z + k • Q) ≠ xco (z + (2 * n + 1 - k') • Q)) := by
  have hz0 : xco z = xco (z + 0 • Q) := by rw [zero_nsmul, add_zero]
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk k' hk' e => ?_, fun k hk k' hk' e => ?_,
    fun k hk k' hk' => ?_⟩
  · rw [Finset.mem_Icc] at hk
    rw [hz0]
    exact good_xco_ne hQ hz (by omega) (by omega)
  · rw [Finset.mem_Icc] at hk
    rw [hz0]
    exact good_xco_ne hQ hz (by omega) (by omega)
  · rw [Finset.coe_Icc, Set.mem_Icc] at hk hk'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact good_xco_ne hQ hz hlt (by omega) e
    · exact good_xco_ne hQ hz hlt (by omega) e.symm
  · rw [Finset.coe_Icc, Set.mem_Icc] at hk hk'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact good_xco_ne hQ hz (j₁ := 2 * n + 1 - k') (j₂ := 2 * n + 1 - k) (by omega) (by omega)
        e.symm
    · exact good_xco_ne hQ hz (j₁ := 2 * n + 1 - k) (j₂ := 2 * n + 1 - k') (by omega) (by omega) e
  · rw [Finset.mem_Icc] at hk hk'
    exact good_xco_ne hQ hz (by omega) (by omega)

end Curve

section Core

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

variable {K' : Type*} [Field K'] [DecidableEq K']

omit [DecidableEq K'] in
private theorem affine_decomp {V : WeierstrassCurve K'} (P : V.toAffine.Point) (hP : P ≠ 0) :
    ∃ h : V.toAffine.Nonsingular (P.coordsOrZero).1 (P.coordsOrZero).2,
      P = .some (P.coordsOrZero).1 (P.coordsOrZero).2 h := by
  rcases P with _ | ⟨a, b, h⟩
  · exact absurd rfl hP
  · exact ⟨h, rfl⟩

private theorem kernel_ne_zero {V : WeierstrassCurve K'} {Q : V.toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 2 * n) : k • Q ≠ 0 := by
  intro h0
  have hdvd : 2 * n + 1 ∣ k := hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
  have := Nat.le_of_dvd (by omega) hdvd
  omega

private theorem sub_nsmul_eq_neg {V : WeierstrassCurve K'} {Q : V.toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) {k : ℕ} (hk : k ≤ 2 * n + 1) :
    (2 * n + 1 - k) • Q = -(k • Q) := by
  have h0 : (2 * n + 1) • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hadd : (2 * n + 1 - k) • Q + k • Q = 0 := by rw [← add_nsmul, Nat.sub_add_cancel hk, h0]
  exact eq_neg_of_add_eq_zero_left hadd

omit [DecidableEq K'] in
private theorem b_model {V : WeierstrassCurve K'} (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) :
    V.b₂ = 4 * V.a₂ ∧ V.b₄ = 2 * V.a₄ ∧ V.b₆ = 4 * V.a₆ ∧ V.b₈ = 4 * V.a₂ * V.a₆ - V.a₄ ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [b₂, ha₁]; ring
  · rw [b₄, ha₁, ha₃]; ring
  · rw [b₆, ha₃]; ring
  · rw [b₈, ha₁, ha₃]; ring

omit [DecidableEq K'] in
private theorem Ψ₂Sq_b_model {V : WeierstrassCurve K'} (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) :
    V.Ψ₂Sq = fP (4 * V.a₂) (2 * V.a₄) (4 * V.a₆) := by
  obtain ⟨hb2, hb4, hb6, -⟩ := b_model ha₁ ha₃
  rw [Ψ₂Sq, hb2, hb4, hb6, fP]

private theorem core_assembly {K : Type*} [Field K] [DecidableEq K] (h2K : (2 : K) ≠ 0)
    (V : WeierstrassCurve K) (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) [V.IsElliptic]
    (e₁ e₂ e₃ : K)
    (hroots : (Cubic.map (RingHom.id K) V.twoTorsionPolynomial).roots = {e₁, e₂, e₃})
    {n : ℕ} (Q : V.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hΔlemma : ∀ (W' : WeierstrassCurve K) (r₁ r₂ r₃ : K),
      (Cubic.map (RingHom.id K) W'.twoTorsionPolynomial).roots = {r₁, r₂, r₃} →
      W'.Δ = 16 * ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2)
    (hσ1 : e₁ + e₂ + e₃ = -V.a₂) (hσ2 : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = V.a₄)
    (hσ3 : e₁ * e₂ * e₃ = -V.a₆)
    (hsumS : ∀ g : K × K → K, ∑ P ∈ V.oddOrderSummingSet Q n, g P
      = ∑ k ∈ Finset.Icc 1 n, g ((k • Q).coordsOrZero))
    (hprodS : ∀ g : K × K → K, ∏ P ∈ V.oddOrderSummingSet Q n, g P
      = ∏ k ∈ Finset.Icc 1 n, g ((k • Q).coordsOrZero))
    (hperm : (Finset.Icc 1 n).val.map (fun k => ((2 : ℕ) • (k • Q)).coordsOrZero.1)
      = (Finset.Icc 1 n).val.map (fun k => ((k : ℕ) • Q).coordsOrZero.1))
    (hC1 : ∀ (P : V.toAffine.Point), (∀ j : ℕ, P + j • Q ≠ 0) →
      (∀ j : ℕ, ∀ k, 1 ≤ k → k ≤ n → ((P + j • Q).coordsOrZero).1 ≠ ((k • Q).coordsOrZero).1) →
      ∀ m : ℕ, Xv (Finset.Icc 1 n) (fun k => ((k • Q).coordsOrZero).1)
          (fun k => V.veluT ((k • Q).coordsOrZero).1 ((k • Q).coordsOrZero).2)
          (fun k => V.veluU ((k • Q).coordsOrZero).1 ((k • Q).coordsOrZero).2)
          (((P + m • Q).coordsOrZero).1)
        = Xv (Finset.Icc 1 n) (fun k => ((k • Q).coordsOrZero).1)
          (fun k => V.veluT ((k • Q).coordsOrZero).1 ((k • Q).coordsOrZero).2)
          (fun k => V.veluU ((k • Q).coordsOrZero).1 ((k • Q).coordsOrZero).2)
          ((P.coordsOrZero).1))
    (hpack : ∀ (xq yq d : K), V.toAffine.Equation xq yq → xq ≠ e₁ → xq ≠ e₂ → xq ≠ e₃ →
      d * (4 * xq ^ 3 + V.b₂ * xq ^ 2 + 2 * V.b₄ * xq + V.b₆)
        = xq ^ 4 - V.b₄ * xq ^ 2 - 2 * V.b₆ * xq - V.b₈ →
      (V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
          + V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
          + V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq) + xq = 4 * d)
      ∧ (V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
            * V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
          + V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
            * V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq)
          + V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
            * V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq)
          + xq * (V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
            + V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
            + V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq))
          = -(V.b₄ + V.b₂ * d))
      ∧ (V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
            * V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
            * V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq)
          + xq * (V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
              * V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
            + V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
              * V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq)
            + V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
              * V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq))
          = 2 * V.b₆ + 2 * V.b₄ * d)
      ∧ (V.toAffine.addX e₁ xq (V.toAffine.slope e₁ xq 0 yq)
            * V.toAffine.addX e₂ xq (V.toAffine.slope e₂ xq 0 yq)
            * V.toAffine.addX e₃ xq (V.toAffine.slope e₃ xq 0 yq) * xq = -(V.b₈ + V.b₆ * d)))
    (hdbl : ∀ (x y : K), V.toAffine.Equation x y → y ≠ V.toAffine.negY x y →
      V.toAffine.addX x x (V.toAffine.slope x x y y)
          * (4 * x ^ 3 + V.b₂ * x ^ 2 + 2 * V.b₄ * x + V.b₆)
        = x ^ 4 - V.b₄ * x ^ 2 - 2 * V.b₆ * x - V.b₈)
    (hL : ∀ (f₁ f₂ f₃ xT yT : K), f₁ + f₂ + f₃ = -V.a₂ → f₁ * f₂ + f₁ * f₃ + f₂ * f₃ = V.a₄ →
      f₁ * f₂ * f₃ = -V.a₆ → V.toAffine.Equation xT yT → xT ≠ f₁ →
      V.toAffine.addX f₁ xT (V.toAffine.slope f₁ xT 0 yT) - f₂ = (f₁ - f₂) * (xT - f₃) / (xT - f₁))
    (hC3 : Set.Infinite {x₀ : K | ∃ z : V.toAffine.Point,
      (∀ j : ℕ, 2 • z + j • Q ≠ 0) ∧ (z.coordsOrZero).1 = x₀}) :
    (V.veluQuotient (V.oddOrderSummingSet Q n)).Δ *
        (∏ P ∈ V.oddOrderSummingSet Q n, V.veluU P.1 P.2) ^ 4
      = V.Δ ^ (2 * n + 1) := by
  classical
  obtain ⟨hb2, hb4, hb6, hb8⟩ := b_model ha₁ ha₃
  have h4 : (4 : K) ≠ 0 := by
    intro h; apply h2K
    have : (2 : K) ^ 2 = 0 := by linear_combination h
    exact pow_eq_zero_iff two_ne_zero |>.mp this

  set S : Finset ℕ := Finset.Icc 1 n with hS
  obtain ⟨x, hx⟩ : ∃ f : ℕ → K, f = fun k => ((k • Q).coordsOrZero).1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ f : ℕ → K, f = fun k => ((k • Q).coordsOrZero).2 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ f : ℕ → K,
    f = fun k => V.veluT ((k • Q).coordsOrZero).1 ((k • Q).coordsOrZero).2 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ f : ℕ → K,
    f = fun k => V.veluU ((k • Q).coordsOrZero).1 ((k • Q).coordsOrZero).2 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ f : ℕ → K, f = fun k => (((2 : ℕ) • (k • Q)).coordsOrZero).1 := ⟨_, rfl⟩
  have hxk : ∀ k, x k = ((k • Q).coordsOrZero).1 := fun k => by rw [hx]
  have hyk : ∀ k, y k = ((k • Q).coordsOrZero).2 := fun k => by rw [hy]
  have htk : ∀ k, t k = V.veluT (x k) (y k) := fun k => by rw [ht, hx, hy]
  have huk : ∀ k, u k = V.veluU (x k) (y k) := fun k => by rw [hu, hx, hy]
  have hdk : ∀ k, d k = (((2 : ℕ) • (k • Q)).coordsOrZero).1 := fun k => by rw [hd]
  rw [← hx, ← hd] at hperm
  rw [← hx, ← ht, ← hu] at hC1
  have hcardS : S.card = n := by simp [hS]
  have hSmem : ∀ {k}, k ∈ S → 1 ≤ k ∧ k ≤ n := fun hk => by simpa [hS] using hk
  have hmemS : ∀ {k}, 1 ≤ k → k ≤ n → k ∈ S := fun h1 h2 => by
    rw [hS]; exact Finset.mem_Icc.mpr ⟨h1, h2⟩

  have hk0 : ∀ k ∈ S, k • Q ≠ 0 := fun k hk =>
    kernel_ne_zero hQ (hSmem hk).1 (by have := (hSmem hk).2; omega)
  have h2k0 : ∀ k ∈ S, (2 : ℕ) • (k • Q) ≠ 0 := fun k hk h => by
    have := hSmem hk
    refine kernel_ne_zero hQ (k := 2 * k) (by omega) (by omega) ?_
    rwa [mul_comm, mul_nsmul]
  have hkpt : ∀ k ∈ S, ∃ h : V.toAffine.Nonsingular (x k) (y k),
      k • Q = .some (x k) (y k) h := by
    intro k hk
    rw [hxk, hyk]
    exact affine_decomp (k • Q) (hk0 k hk)
  have hkeq : ∀ k ∈ S, V.toAffine.Equation (x k) (y k) := fun k hk => by
    obtain ⟨h, -⟩ := hkpt k hk
    exact h.1
  have hkny : ∀ k ∈ S, y k ≠ V.toAffine.negY (x k) (y k) := by
    intro k hk hyy
    obtain ⟨h, hke⟩ := hkpt k hk
    apply h2k0 k hk
    rw [two_nsmul, hke]
    exact Affine.Point.add_self_of_Y_eq hyy
  have hdk' : ∀ k ∈ S, d k
      = V.toAffine.addX (x k) (x k) (V.toAffine.slope (x k) (x k) (y k) (y k)) := by
    intro k hk
    obtain ⟨h, hke⟩ := hkpt k hk
    rw [hdk, two_nsmul, hke, Affine.Point.add_self_of_Y_ne (hkny k hk)]
    rfl
  have ht' : ∀ k ∈ S, t k = 6 * x k ^ 2 + 4 * V.a₂ * x k + 2 * V.a₄ := fun k _ => by
    rw [htk, veluT_eq, hb2, hb4]
  have hu' : ∀ k ∈ S, u k
      = 4 * x k ^ 3 + 4 * V.a₂ * x k ^ 2 + 2 * (2 * V.a₄) * x k + 4 * V.a₆ := fun k hk => by
    rw [huk, V.veluU_eq_Ψ₂Sq_eval (hkeq k hk), Ψ₂Sq_b_model ha₁ ha₃, fP]
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]

  have hP4 : V.twoTorsionPolynomial.toPoly ≠ 0 :=
    Cubic.ne_zero_of_a_ne_zero (show V.twoTorsionPolynomial.a ≠ 0 from h4)
  have hΨV : V.Ψ₂Sq = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)) := by
    have e := Cubic.eq_prod_three_roots (φ := RingHom.id K) (P := V.twoTorsionPolynomial)
      (show V.twoTorsionPolynomial.a ≠ 0 from h4) hroots
    rw [Cubic.map_toPoly, Polynomial.map_id, ← Ψ₂Sq_eq] at e
    rw [e, show V.twoTorsionPolynomial.a = 4 from rfl, RingHom.id_apply]
    ring
  have heroot : ∀ e ∈ ({e₁, e₂, e₃} : Multiset K), V.toAffine.Equation e 0 := by
    intro e he
    have hmem : e ∈ (Cubic.map (RingHom.id K) V.twoTorsionPolynomial).roots := by
      rw [hroots]; exact he
    rw [Cubic.map_roots, Polynomial.map_id, Polynomial.mem_roots hP4, IsRoot.def, ← Ψ₂Sq_eq,
      hΨV] at hmem
    simp only [eval_mul, eval_C, eval_sub, eval_X] at hmem
    have h' : (e - e₁) * (e - e₂) * (e - e₃) = 0 := (mul_eq_zero.mp hmem).resolve_left h4
    rw [Affine.equation_iff, ha₁, ha₃]
    linear_combination -h' - e ^ 2 * hσ1 + e * hσ2 - hσ3
  have he₁eq : V.toAffine.Equation e₁ 0 := heroot e₁ (by simp)
  have he₂eq : V.toAffine.Equation e₂ 0 := heroot e₂ (by simp)
  have he₃eq : V.toAffine.Equation e₃ 0 := heroot e₃ (by simp)
  have hens : ∀ e, V.toAffine.Equation e 0 → V.toAffine.Nonsingular e 0 := fun e he =>
    (Affine.equation_iff_nonsingular (W := V)).mp he
  have he_ne : ∀ e, V.toAffine.Equation e 0 → ∀ k ∈ S, e ≠ x k := by
    intro e he k hk hex
    have hT : V.toAffine.Nonsingular e 0 := hens e he
    obtain ⟨h, hke⟩ := hkpt k hk
    have hx' : xco (Affine.Point.some e 0 hT) = xco (k • Q) := by rw [hke]; exact hex
    have hT2 : (Affine.Point.some e 0 hT : V.toAffine.Point) + Affine.Point.some e 0 hT = 0 :=
      Affine.Point.add_self_of_Y_eq (by simp [Affine.negY, toAffine, ha₁, ha₃])
    rcases eq_or_eq_neg_of_xco_eq (Affine.Point.some_ne_zero hT) (hk0 k hk) hx' with ek | ek
    · apply h2k0 k hk
      rw [two_nsmul, ← ek, hT2]
    · apply h2k0 k hk
      rw [two_nsmul, show k • Q = -(Affine.Point.some e 0 hT) by rw [ek, neg_neg], ← neg_add,
        hT2, neg_zero]

  have hMP : MM S x t u V.a₂ V.a₄ V.a₆ = PP S x t u := by
    refine MM_eq_PP_of_infinite S x t u V.a₂ V.a₄ V.a₆ (hC3.mono ?_)
    rintro x₀ ⟨z, hz, rfl⟩
    simp only [Set.mem_setOf_eq]
    have hz0 : z ≠ 0 := fun h => hz 0 (by rw [h, nsmul_zero, zero_nsmul, add_zero])
    obtain ⟨h₀, hzeq⟩ := affine_decomp z hz0
    set x₀ := (z.coordsOrZero).1 with hx₀
    set y₀ := (z.coordsOrZero).2 with hy₀
    have hxne : ∀ j : ℕ, ∀ k ∈ S, ((z + j • Q).coordsOrZero).1 ≠ x k := by
      intro j k hk
      rw [hxk]
      exact good_xco_ne_kernel hQ hz j k (hSmem hk).1 (by have := (hSmem hk).2; omega)
    have hx0ne : ∀ k ∈ S, x₀ ≠ x k := by
      intro k hk
      have := hxne 0 k hk
      rwa [zero_nsmul, add_zero] at this
    set τp : ℕ → K := fun k => ((z + k • Q).coordsOrZero).1 with hτp
    set τm : ℕ → K := fun k => ((z + (2 * n + 1 - k) • Q).coordsOrZero).1 with hτm
    have hτp' : ∀ k ∈ S, τp k
        = V.toAffine.addX x₀ (x k) (V.toAffine.slope x₀ (x k) y₀ (y k)) := by
      intro k hk
      obtain ⟨h, hke⟩ := hkpt k hk
      simp only [hτp]
      rw [hzeq, hke, Affine.Point.add_of_X_ne (hx0ne k hk)]
      rfl
    have hτm' : ∀ k ∈ S, τm k = V.toAffine.addX x₀ (x k)
        (V.toAffine.slope x₀ (x k) y₀ (V.toAffine.negY (x k) (y k))) := by
      intro k hk
      obtain ⟨h, hke⟩ := hkpt k hk
      simp only [hτm]
      rw [sub_nsmul_eq_neg hQ (by have := (hSmem hk).2; omega), hzeq, hke,
        Affine.Point.neg_some, Affine.Point.add_of_X_ne (hx0ne k hk)]
      rfl
    have hsum : ∀ k ∈ S, τp k + τm k = 2 * x k + t k / (x₀ - x k) + u k / (x₀ - x k) ^ 2 := by
      intro k hk
      rw [hτp' k hk, hτm' k hk, htk, huk]
      exact N5IDAux4.chord_sum' V h₀.1 (hkeq k hk) (hx0ne k hk)
    have hprod : ∀ k ∈ S, τp k * τm k
        = ((x₀ * x k - V.a₄) ^ 2 - 4 * V.a₆ * (x₀ + x k + V.a₂)) / (x₀ - x k) ^ 2 := by
      intro k hk
      rw [hτp' k hk, hτm' k hk]
      exact N5IDAux4.chord_prod V ha₁ ha₃ h₀.1 (hkeq k hk) (hx0ne k hk)

    set c := Xv S x t u x₀ with hc
    have hzj : ∀ j : ℕ, z + j • Q ≠ 0 := good_add_nsmul_ne_zero hz
    have hC1z := hC1 z hzj (fun j k hk1 hkn =>
      good_xco_ne_kernel hQ hz j k hk1 (by omega))
    have hAv : ∀ v, (∀ k ∈ S, v ≠ x k) → Xv S x t u v = c →
        (AP S x t u).eval v = c * (hP S x).eval v ^ 2 := by
      intro v hv hXv
      rw [AP_eval S x t u v hv, hXv, mul_comm]
    have hr0 : (AP S x t u).eval x₀ = c * (hP S x).eval x₀ ^ 2 := hAv x₀ hx0ne rfl
    have hrp : ∀ k ∈ S, (AP S x t u).eval (τp k) = c * (hP S x).eval (τp k) ^ 2 :=
      fun k _ => hAv (τp k) (hxne k) (hC1z k)
    have hrm : ∀ k ∈ S, (AP S x t u).eval (τm k) = c * (hP S x).eval (τm k) ^ 2 :=
      fun k _ => hAv (τm k) (hxne (2 * n + 1 - k)) (hC1z (2 * n + 1 - k))
    obtain ⟨hd0p, hd0m, hinjp, hinjm, hpm⟩ := good_distinct (V := V) hQ hz
    have hnorm := norm_identity' S x t u x₀ c τp τm hd0p hd0m hinjp hinjm hpm hr0 hrp hrm
    exact spec_MM_eq_spec_PP_at S x t u V.a₂ V.a₄ V.a₆ x₀ c τp τm hx0ne hsum hprod hnorm hr0.symm

  obtain ⟨ξ₁, hξ₁⟩ : ∃ f : ℕ → K,
    f = fun k => V.toAffine.addX e₁ (x k) (V.toAffine.slope e₁ (x k) 0 (y k)) := ⟨_, rfl⟩
  obtain ⟨ξ₂, hξ₂⟩ : ∃ f : ℕ → K,
    f = fun k => V.toAffine.addX e₂ (x k) (V.toAffine.slope e₂ (x k) 0 (y k)) := ⟨_, rfl⟩
  obtain ⟨ξ₃, hξ₃⟩ : ∃ f : ℕ → K,
    f = fun k => V.toAffine.addX e₃ (x k) (V.toAffine.slope e₃ (x k) 0 (y k)) := ⟨_, rfl⟩
  have hξ₁k : ∀ k, ξ₁ k = V.toAffine.addX e₁ (x k) (V.toAffine.slope e₁ (x k) 0 (y k)) :=
    fun k => by rw [hξ₁]
  have hξ₂k : ∀ k, ξ₂ k = V.toAffine.addX e₂ (x k) (V.toAffine.slope e₂ (x k) 0 (y k)) :=
    fun k => by rw [hξ₂]
  have hξ₃k : ∀ k, ξ₃ k = V.toAffine.addX e₃ (x k) (V.toAffine.slope e₃ (x k) 0 (y k)) :=
    fun k => by rw [hξ₃]
  have hfac : ∀ e, V.toAffine.Equation e 0 → ∀ k ∈ S,
      C ((e - x k) ^ 2) * X ^ 2 - C ((SqP x t u k).eval e) * X + C ((PqP x V.a₂ V.a₄ V.a₆ k).eval e)
        = C ((e - x k) ^ 2)
          * (X - C (V.toAffine.addX e (x k) (V.toAffine.slope e (x k) 0 (y k)))) ^ 2 := by
    intro e he k hk
    rw [eval_SqP, eval_PqP, htk, huk]
    exact two_torsion_chord_factor ha₁ ha₃ he (hkeq k hk) (he_ne e he k hk)
  have hfac₁ : ∀ k ∈ S, C ((e₁ - x k) ^ 2) * X ^ 2 - C ((SqP x t u k).eval e₁) * X
      + C ((PqP x V.a₂ V.a₄ V.a₆ k).eval e₁) = C ((e₁ - x k) ^ 2) * (X - C (ξ₁ k)) ^ 2 :=
    fun k hk => by rw [hξ₁k]; exact hfac e₁ he₁eq k hk
  have hfac₂ : ∀ k ∈ S, C ((e₂ - x k) ^ 2) * X ^ 2 - C ((SqP x t u k).eval e₂) * X
      + C ((PqP x V.a₂ V.a₄ V.a₆ k).eval e₂) = C ((e₂ - x k) ^ 2) * (X - C (ξ₂ k)) ^ 2 :=
    fun k hk => by rw [hξ₂k]; exact hfac e₂ he₂eq k hk
  have hfac₃ : ∀ k ∈ S, C ((e₃ - x k) ^ 2) * X ^ 2 - C ((SqP x t u k).eval e₃) * X
      + C ((PqP x V.a₂ V.a₄ V.a₆ k).eval e₃) = C ((e₃ - x k) ^ 2) * (X - C (ξ₃ k)) ^ 2 :=
    fun k hk => by rw [hξ₃k]; exact hfac e₃ he₃eq k hk
  have fib₁ := fiber S x t u V.a₂ V.a₄ V.a₆ hMP e₁ ξ₁ (he_ne e₁ he₁eq) hfac₁
  have fib₂ := fiber S x t u V.a₂ V.a₄ V.a₆ hMP e₂ ξ₂ (he_ne e₂ he₂eq) hfac₂
  have hvieta : fP (4 * V.a₂) (2 * V.a₄) (4 * V.a₆) = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)) := by
    rw [← Ψ₂Sq_b_model ha₁ ha₃, hΨV]

  have hpk : ∀ k ∈ S, (X - C (ξ₁ k)) * (X - C (ξ₂ k)) * (X - C (ξ₃ k)) * (X - C (x k))
      = φP (2 * V.a₄) (4 * V.a₆) (4 * V.a₂ * V.a₆ - V.a₄ ^ 2)
        - C (d k) * fP (4 * V.a₂) (2 * V.a₄) (4 * V.a₆) := by
    intro k hk
    have hne : ∀ e, V.toAffine.Equation e 0 → x k ≠ e := fun e he => (he_ne e he k hk).symm
    have hdd : d k * (4 * x k ^ 3 + V.b₂ * x k ^ 2 + 2 * V.b₄ * x k + V.b₆)
        = x k ^ 4 - V.b₄ * x k ^ 2 - 2 * V.b₆ * x k - V.b₈ := by
      rw [hdk' k hk]; exact hdbl (x k) (y k) (hkeq k hk) (hkny k hk)
    obtain ⟨s1, s2, s3, s4⟩ := hpack (x k) (y k) (d k) (hkeq k hk) (hne e₁ he₁eq) (hne e₂ he₂eq)
      (hne e₃ he₃eq) hdd
    rw [hξ₁k, hξ₂k, hξ₃k]
    generalize V.toAffine.addX e₁ (x k) (V.toAffine.slope e₁ (x k) 0 (y k)) = A₁ at s1 s2 s3 s4 ⊢
    generalize V.toAffine.addX e₂ (x k) (V.toAffine.slope e₂ (x k) 0 (y k)) = A₂ at s1 s2 s3 s4 ⊢
    generalize V.toAffine.addX e₃ (x k) (V.toAffine.slope e₃ (x k) 0 (y k)) = A₃ at s1 s2 s3 s4 ⊢
    simp only [hb2, hb4, hb6, hb8] at s2 s3 s4
    have eL : (X - C A₁) * (X - C A₂) * (X - C A₃) * (X - C (x k))
        = X ^ 4 - C (A₁ + A₂ + A₃ + x k) * X ^ 3
          + C (A₁ * A₂ + A₁ * A₃ + A₂ * A₃ + x k * (A₁ + A₂ + A₃)) * X ^ 2
          - C (A₁ * A₂ * A₃ + x k * (A₁ * A₂ + A₁ * A₃ + A₂ * A₃)) * X
          + C (A₁ * A₂ * A₃ * x k) := by
      simp only [map_add, map_mul]
      ring
    rw [eL, s1, s2, s3, s4, φP, fP]
    simp only [map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat]
    ring

  have hcubic := pipeline S x d t u ξ₁ ξ₂ ξ₃ V.a₂ V.a₄ V.a₆ e₁ e₂ e₃ hMP (he_ne e₁ he₁eq)
    (he_ne e₂ he₂eq) (he_ne e₃ he₃eq) hfac₁ hfac₂ hfac₃ hvieta ht' hu' hperm hpk
  have htS : V.veluTSum (V.oddOrderSummingSet Q n) = ∑ k ∈ S, t k := by
    rw [veluTSum, hsumS]
    exact Finset.sum_congr rfl fun k _ => by rw [htk, hxk, hyk]
  have hwS : V.veluWSum (V.oddOrderSummingSet Q n) = ∑ k ∈ S, (u k + x k * t k) := by
    rw [veluWSum, hsumS]
    exact Finset.sum_congr rfl fun k _ => by rw [huk, htk, hxk, hyk]; rfl
  have hΨ' : (V.veluQuotient (V.oddOrderSummingSet Q n)).Ψ₂Sq
      = C 4 * ((X - C (Xv S x t u e₁)) * (X - C (Xv S x t u e₂)) * (X - C (Xv S x t u e₃))) := by
    rw [Ψ₂Sq, veluQuotient_b₂, veluQuotient_b₄, veluQuotient_b₆, htS, hwS, hb2, hb4, hb6]
    exact hcubic.symm
  have hroots' : (Cubic.map (RingHom.id K)
      (V.veluQuotient (V.oddOrderSummingSet Q n)).twoTorsionPolynomial).roots
        = {Xv S x t u e₁, Xv S x t u e₂, Xv S x t u e₃} := by
    rw [Cubic.map_roots, Polynomial.map_id, ← Ψ₂Sq_eq, hΨ', roots_cubic _ _ _ h4]
  have hΔ' := hΔlemma _ _ _ _ hroots'
  have hΔ := hΔlemma _ _ _ _ hroots

  have hA : ∀ e, V.toAffine.Equation e 0 →
      (AP S x t u).eval e = (hP S x).eval e ^ 2 * Xv S x t u e :=
    fun e he => AP_eval S x t u e (he_ne e he)
  have hFev : ∀ (e e' X₀ : K) (ξ : ℕ → K),
      AP S x t u - C X₀ * hP S x ^ 2 = (X - C e) * (∏ q ∈ S, (X - C (ξ q))) ^ 2 →
      (AP S x t u).eval e' - X₀ * (hP S x).eval e' ^ 2 = (e' - e) * (∏ q ∈ S, (e' - ξ q)) ^ 2 := by
    intro e e' X₀ ξ hF
    have := congrArg (Polynomial.eval e') hF
    simpa only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_prod] using this
  have hL' : ∀ (f₁ f₂ f₃ : K), f₁ + f₂ + f₃ = -V.a₂ → f₁ * f₂ + f₁ * f₃ + f₂ * f₃ = V.a₄ →
      f₁ * f₂ * f₃ = -V.a₆ → V.toAffine.Equation f₁ 0 → ∀ k ∈ S,
      (f₂ - V.toAffine.addX f₁ (x k) (V.toAffine.slope f₁ (x k) 0 (y k))) * (x k - f₁)
        = -((f₁ - f₂) * (x k - f₃)) := by
    intro f₁ f₂ f₃ h1 h2 h3 hf₁ k hk
    have hne : x k ≠ f₁ := (he_ne f₁ hf₁ k hk).symm
    have hsub : x k - f₁ ≠ 0 := sub_ne_zero.mpr hne
    have e := hL f₁ f₂ f₃ (x k) (y k) h1 h2 h3 (hkeq k hk) hne
    have e' : (V.toAffine.addX f₁ (x k) (V.toAffine.slope f₁ (x k) 0 (y k)) - f₂) * (x k - f₁)
        = (f₁ - f₂) * (x k - f₃) := by
      rw [e, div_mul_cancel₀ _ hsub]
    linear_combination -e'
  have hL₁₂ := hL' e₁ e₂ e₃ hσ1 hσ2 hσ3 he₁eq
  have hL₁₃ := hL' e₁ e₃ e₂ (by linear_combination hσ1) (by linear_combination hσ2)
    (by linear_combination hσ3) he₁eq
  have hL₂₃ := hL' e₂ e₃ e₁ (by linear_combination hσ1) (by linear_combination hσ2)
    (by linear_combination hσ3) he₂eq
  have hu4 : ∀ k ∈ S, u k = 4 * ((x k - e₁) * (x k - e₂) * (x k - e₃)) := fun k hk => by
    rw [huk, V.veluU_eq_Ψ₂Sq_eval (hkeq k hk), hΨV]
    simp only [eval_mul, eval_C, eval_sub, eval_X]
  have key := delta_identity S x t u ξ₁ ξ₂ e₁ e₂ e₃ (Xv S x t u e₁) (Xv S x t u e₂)
    (Xv S x t u e₃) V.Δ (V.veluQuotient (V.oddOrderSummingSet Q n)).Δ (hA e₂ he₂eq)
    (hA e₃ he₃eq) (hFev e₁ e₂ _ ξ₁ fib₁) (hFev e₁ e₃ _ ξ₁ fib₁) (hFev e₂ e₃ _ ξ₂ fib₂)
    (fun k hk => by rw [hξ₁k]; exact hL₁₂ k hk) (fun k hk => by rw [hξ₁k]; exact hL₁₃ k hk)
    (fun k hk => by rw [hξ₂k]; exact hL₂₃ k hk)
    (he_ne e₁ he₁eq) (he_ne e₂ he₂eq) (he_ne e₃ he₃eq) hu4 hΔ hΔ'
  have hU : ∏ P ∈ V.oddOrderSummingSet Q n, V.veluU P.1 P.2 = ∏ k ∈ S, u k := by
    rw [hprodS]
    exact Finset.prod_congr rfl fun k _ => by rw [huk, hxk, hyk]
  rw [hcardS] at key
  rw [hU]
  exact key

end Core

section C3

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

variable {K : Type*} [Field K] [DecidableEq K] {V : WeierstrassCurve K}

private theorem two_torsion_finite (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) (h2K : (2 : K) ≠ 0)
    (h4 : (4 : K) ≠ 0) : {P : V.toAffine.Point | 2 • P = 0}.Finite := by
  classical
  have hΨ0 : V.Ψ₂Sq ≠ 0 := by
    rw [Ψ₂Sq_eq]; exact Cubic.ne_zero_of_a_ne_zero (show V.twoTorsionPolynomial.a ≠ 0 from h4)
  refine ((Set.Finite.image (fun e => if h : V.toAffine.Nonsingular e 0 then Affine.Point.some e 0 h
    else (0 : V.toAffine.Point)) (V.Ψ₂Sq.roots.toFinset.finite_toSet)).insert 0).subset ?_
  intro P hP
  simp only [Set.mem_setOf_eq] at hP
  rcases P with _ | ⟨a, b, hab⟩
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    have hy : b = V.toAffine.negY a b := by
      by_contra hne
      rw [two_nsmul, Affine.Point.add_self_of_Y_ne hne] at hP
      exact Affine.Point.some_ne_zero _ hP
    have hb : b = 0 := by
      simp only [Affine.negY, toAffine, ha₁, ha₃, zero_mul, sub_zero] at hy
      have h2b : (2 : K) * b = 0 := by linear_combination hy
      exact (mul_eq_zero.mp h2b).resolve_left h2K
    subst hb
    refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hΨ0, IsRoot.def,
        ← V.veluU_eq_Ψ₂Sq_eval hab.1]
      simp [veluU, veluGy, ha₁, ha₃]
    · simp only [dif_pos hab]

private theorem doubling_fibre_finite (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) (h2K : (2 : K) ≠ 0)
    (h4 : (4 : K) ≠ 0) (w : V.toAffine.Point) : {z : V.toAffine.Point | 2 • z = w}.Finite := by
  by_cases hne : {z : V.toAffine.Point | 2 • z = w}.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    refine Set.Finite.of_finite_image (f := fun z => z - z₀) ?_ sub_left_injective.injOn
    refine (two_torsion_finite ha₁ ha₃ h2K h4).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_setOf_eq] at hz hz₀ ⊢
    rw [nsmul_sub, hz, hz₀, sub_self]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Set.finite_empty

private theorem bad_finite (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) (h2K : (2 : K) ≠ 0) (h4 : (4 : K) ≠ 0)
    {Q : V.toAffine.Point} {n : ℕ} (hQ : addOrderOf Q = 2 * n + 1) :
    {z : V.toAffine.Point | ∃ j : ℕ, 2 • z + j • Q = 0}.Finite := by
  have hsub : {z : V.toAffine.Point | ∃ j : ℕ, 2 • z + j • Q = 0}
      ⊆ ⋃ j ∈ Set.Iio (2 * n + 1), {z | 2 • z = -(j • Q)} := by
    rintro z ⟨j, hj⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Iio]
    refine ⟨j % (2 * n + 1), Nat.mod_lt _ (by omega), ?_⟩
    rw [← hQ, mod_addOrderOf_nsmul]
    exact eq_neg_of_add_eq_zero_left hj
  exact ((Set.finite_Iio _).biUnion fun j _ => doubling_fibre_finite ha₁ ha₃ h2K h4 _).subset hsub

private theorem good_abscissae_infinite [IsAlgClosed K] [V.IsElliptic] (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0)
    (h2K : (2 : K) ≠ 0) {Q : V.toAffine.Point} {n : ℕ} (hQ : addOrderOf Q = 2 * n + 1) :
    Set.Infinite {x₀ : K | ∃ z : V.toAffine.Point,
      (∀ j : ℕ, 2 • z + j • Q ≠ 0) ∧ (z.coordsOrZero).1 = x₀} := by
  have h4 : (4 : K) ≠ 0 := by
    intro h; apply h2K
    have : (2 : K) ^ 2 = 0 := by linear_combination h
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have hlift : ∀ x₀ : K, ∃ y₀, V.toAffine.Nonsingular x₀ y₀ := by
    intro x₀
    obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_pow_nat_eq
      (x₀ ^ 3 + V.a₂ * x₀ ^ 2 + V.a₄ * x₀ + V.a₆) (by norm_num : 0 < 2)
    refine ⟨y₀, (Affine.equation_iff_nonsingular (W := V)).mp ?_⟩
    rw [Affine.equation_iff, ha₁, ha₃]
    linear_combination hy₀
  choose lift hlift using hlift
  have hinj : Function.Injective (fun x₀ => (Affine.Point.some x₀ (lift x₀) (hlift x₀) :
      V.toAffine.Point)) := by
    intro a b h
    have := congrArg (fun P : V.toAffine.Point => (P.coordsOrZero).1) h
    simpa using this
  have hfin := (bad_finite ha₁ ha₃ h2K h4 hQ).preimage hinj.injOn
  refine (Set.infinite_univ.diff hfin).mono ?_
  rintro x₀ ⟨-, hx₀⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq, not_exists] at hx₀
  exact ⟨_, hx₀, rfl⟩

end C3

section CharTwo

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in

private theorem Δ_of_char_two (W : WeierstrassCurve F) (h2 : (2 : F) = 0) (ha₁ : W.a₁ = 0) :
    W.Δ = W.a₃ ^ 4 := by
  rw [Δ, b₂, b₄, b₆, b₈, ha₁]
  linear_combination (-216 * W.a₆ ^ 2 - 32 * W.a₄ ^ 3 - 108 * W.a₃ ^ 2 * W.a₆ - 14 * W.a₃ ^ 4
    + 144 * W.a₂ * W.a₄ * W.a₆ + 36 * W.a₂ * W.a₃ ^ 2 * W.a₄ + 8 * W.a₂ ^ 2 * W.a₄ ^ 2
    - 32 * W.a₂ ^ 3 * W.a₆ - 8 * W.a₂ ^ 3 * W.a₃ ^ 2) * h2

private theorem char_two_a₁_zero (W : WeierstrassCurve F) (h2 : (2 : F) = 0) (ha₁ : W.a₁ = 0) {n : ℕ}
    (Q : W.toAffine.Point) (hcard : (W.oddOrderSummingSet Q n).card = n) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ *
        (∏ P ∈ W.oddOrderSummingSet Q n, W.veluU P.1 P.2) ^ 4
      = W.Δ ^ (2 * n + 1) := by
  have hU : ∀ P ∈ W.oddOrderSummingSet Q n, W.veluU P.1 P.2 = W.a₃ ^ 2 := by
    intro P _
    simp only [veluU, veluGy, ha₁, zero_mul, add_zero]
    rw [show (2 : F) * P.2 = 0 by rw [h2, zero_mul], zero_add]
    ring
  have hprod : ∏ P ∈ W.oddOrderSummingSet Q n, W.veluU P.1 P.2 = (W.a₃ ^ 2) ^ n := by
    rw [Finset.prod_congr rfl hU, Finset.prod_const, hcard]
  have hΔ := Δ_of_char_two W h2 ha₁
  have hΔ' := Δ_of_char_two (W.veluQuotient (W.oddOrderSummingSet Q n)) h2
    (by rw [veluQuotient_a₁, ha₁])
  rw [hprod, hΔ', veluQuotient_a₃, hΔ]
  ring

end CharTwo

section CharTwoOrdAlgebra

variable {K : Type*} [Field K]

private theorem neg_eq_self_of_two (h2 : (2 : K) = 0) (a : K) : -a = a := by
  linear_combination (-a) * h2

private theorem sub_sq_of_two (h2 : (2 : K) = 0) (a b : K) : (a - b) ^ 2 = a ^ 2 - b ^ 2 := by
  linear_combination (-b * (a - b)) * h2

private theorem sum_sq_of_two (h2 : (2 : K) = 0) {ι : Type*} (s : Finset ι) (f : ι → K) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, ← ih]
    linear_combination (f a * ∑ i ∈ s, f i) * h2

variable {ι : Type*} [DecidableEq ι] (I : Finset ι) (x Y : ι → K)

private noncomputable def BtP : K[X] :=
  ∏ i ∈ I, (X - C (x i ^ 2)) + ∑ j ∈ I, C (x j) * ∏ i ∈ I.erase j, (X - C (x i ^ 2))

omit [DecidableEq ι] in
private theorem monic_prod_X_sub_C' (s : Finset ι) (g : ι → K) :
    (∏ i ∈ s, (X - C (g i))).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

omit [DecidableEq ι] in
private theorem natDegree_prod_X_sub_C' (s : Finset ι) (g : ι → K) :
    (∏ i ∈ s, (X - C (g i))).natDegree = s.card := by
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

private theorem BtP_eval (v : K) : (BtP I x).eval v
    = ∏ i ∈ I, (v - x i ^ 2) + ∑ j ∈ I, x j * ∏ i ∈ I.erase j, (v - x i ^ 2) := by
  simp only [BtP, eval_add, eval_prod, eval_finsetSum, eval_mul, eval_sub, eval_X, eval_C]

private theorem BtP_eq_prod (hI : I.Nonempty) (hinj : Set.InjOn Y I)
    (hroot : ∀ k ∈ I, (BtP I x).eval (Y k) = 0) :
    BtP I x = ∏ k ∈ I, (X - C (Y k)) := by
  have hmon1 := monic_prod_X_sub_C' I (fun i => x i ^ 2)
  have hmonR := monic_prod_X_sub_C' I Y
  have hdeg1 := natDegree_prod_X_sub_C' I (fun i => x i ^ 2)
  have hdegR := natDegree_prod_X_sub_C' I Y
  have htail : (∑ j ∈ I, C (x j) * ∏ i ∈ I.erase j, (X - C (x i ^ 2))).natDegree
      ≤ I.card - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_prod_X_sub_C' (I.erase j) (fun i => x i ^ 2), card_erase_of_mem hj]
  refine eq_of_degree_sub_lt_of_eval_index_eq I hinj ?_ fun k hk => ?_
  · have e : BtP I x - ∏ k ∈ I, (X - C (Y k))
        = (∏ i ∈ I, (X - C (x i ^ 2)) - ∏ k ∈ I, (X - C (Y k)))
          + ∑ j ∈ I, C (x j) * ∏ i ∈ I.erase j, (X - C (x i ^ 2)) := by
      rw [BtP]; ring
    rw [e]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · by_cases h0 : ∏ i ∈ I, (X - C (x i ^ 2)) - ∏ k ∈ I, (X - C (Y k)) = 0
      · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
      have := degree_sub_lt (p := ∏ i ∈ I, (X - C (x i ^ 2))) (q := ∏ k ∈ I, (X - C (Y k)))
        (by rw [degree_eq_natDegree hmon1.ne_zero, degree_eq_natDegree hmonR.ne_zero,
          hdeg1, hdegR]) hmon1.ne_zero (by rw [hmon1.leadingCoeff, hmonR.leadingCoeff])
      rwa [degree_eq_natDegree hmon1.ne_zero, hdeg1] at this
    · refine lt_of_le_of_lt (degree_le_of_natDegree_le htail) ?_
      exact_mod_cast Nat.sub_lt (card_pos.mpr hI) one_pos
  · rw [hroot k hk, eval_prod]
    exact (prod_eq_zero hk (by simp)).symm

omit [DecidableEq ι] in

private theorem one_add_sum_eq_zero (h2 : (2 : K) = 0) {ξ : K} (hξ0 : ξ ≠ 0)
    (hξx : ∀ j ∈ I, ξ ≠ x j)
    (hvan : ξ + ∑ j ∈ I, (x j / (ξ - x j) + x j ^ 2 / (ξ - x j) ^ 2) = 0) :
    1 + ∑ j ∈ I, x j / (ξ ^ 2 - x j ^ 2) = 0 := by
  have hsum : ∑ j ∈ I, (x j / (ξ - x j) + x j ^ 2 / (ξ - x j) ^ 2)
      = ξ * ∑ j ∈ I, x j / (ξ ^ 2 - x j ^ 2) := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hd : ξ - x j ≠ 0 := sub_ne_zero.mpr (hξx j hj)
    rw [← sub_sq_of_two h2 ξ (x j)]
    field_simp
    ring
  rw [hsum, ← mul_one_add] at hvan
  exact (mul_eq_zero.mp hvan).resolve_left hξ0

private theorem BtP_eval_eq_zero {v : K} (hvx : ∀ j ∈ I, v - x j ^ 2 ≠ 0)
    (h : 1 + ∑ j ∈ I, x j / (v - x j ^ 2) = 0) : (BtP I x).eval v = 0 := by
  rw [BtP_eval]
  have hPe : ∀ j ∈ I, ∏ i ∈ I.erase j, (v - x i ^ 2)
      = (∏ i ∈ I, (v - x i ^ 2)) / (v - x j ^ 2) := by
    intro j hj
    rw [eq_div_iff (hvx j hj), mul_comm]
    exact mul_prod_erase I (fun i => v - x i ^ 2) hj
  have hs : ∑ j ∈ I, x j * ∏ i ∈ I.erase j, (v - x i ^ 2)
      = (∏ i ∈ I, (v - x i ^ 2)) * ∑ j ∈ I, x j / (v - x j ^ 2) := by
    rw [mul_sum]
    exact sum_congr rfl fun j hj => by rw [hPe j hj]; ring
  rw [hs, ← mul_one_add, h, mul_zero]

private theorem read_zero (h2 : (2 : K) = 0) (hBR : BtP I x = ∏ k ∈ I, (X - C (Y k))) :
    ∏ i ∈ I, x i ^ 2 + ∑ j ∈ I, x j * ∏ i ∈ I.erase j, x i ^ 2 = ∏ k ∈ I, Y k := by
  have e := congrArg (eval 0) hBR
  rw [BtP_eval, eval_prod] at e
  simpa only [eval_sub, eval_X, eval_C, zero_sub, neg_eq_self_of_two h2] using e

private theorem read_pred (h2 : (2 : K) = 0) (hI : I.Nonempty)
    (hBR : BtP I x = ∏ k ∈ I, (X - C (Y k))) :
    ∑ i ∈ I, x i ^ 2 + ∑ j ∈ I, x j = ∑ k ∈ I, Y k := by
  have hpos : 0 < I.card := card_pos.mpr hI
  have e := congrArg (fun p : K[X] => p.coeff (I.card - 1)) hBR
  simp only [BtP, coeff_add, finsetSum_coeff, coeff_C_mul] at e
  have c1 : (∏ i ∈ I, (X - C (x i ^ 2))).coeff (I.card - 1) = -∑ i ∈ I, x i ^ 2 :=
    prod_X_sub_C_coeff_card_pred I (fun i => x i ^ 2) hpos
  have cR : (∏ k ∈ I, (X - C (Y k))).coeff (I.card - 1) = -∑ k ∈ I, Y k :=
    prod_X_sub_C_coeff_card_pred I Y hpos
  have hlead : ∀ j ∈ I, (∏ i ∈ I.erase j, (X - C (x i ^ 2))).coeff (I.card - 1) = 1 := by
    intro j hj
    rw [← card_erase_of_mem hj, ← natDegree_prod_X_sub_C' (I.erase j) (fun i => x i ^ 2)]
    exact (monic_prod_X_sub_C' (I.erase j) (fun i => x i ^ 2)).coeff_natDegree
  have hs : ∑ j ∈ I, x j * (∏ i ∈ I.erase j, (X - C (x i ^ 2))).coeff (I.card - 1)
      = ∑ j ∈ I, x j := sum_congr rfl fun j hj => by rw [hlead j hj, mul_one]
  rw [c1, cR, hs] at e
  linear_combination -e + (∑ j ∈ I, x j) * h2

private theorem close_of_reads (h2 : (2 : K) = 0) (a₆ : K)
    (hx0 : ∀ k ∈ I, x k ≠ 0) (hY : ∀ k ∈ I, Y k = a₆ / x k ^ 2)
    (r0 : ∏ i ∈ I, x i ^ 2 + ∑ j ∈ I, x j * ∏ i ∈ I.erase j, x i ^ 2 = ∏ k ∈ I, Y k)
    (r1 : ∑ i ∈ I, x i ^ 2 + ∑ j ∈ I, x j = ∑ k ∈ I, Y k) :
    (a₆ + ∑ k ∈ I, x k + (∑ k ∈ I, x k) ^ 2) * (∏ k ∈ I, x k ^ 2) ^ 4
      = a₆ ^ (2 * I.card + 1) := by
  have hP20 : ∏ k ∈ I, x k ^ 2 ≠ 0 := prod_ne_zero_iff.mpr fun k hk => pow_ne_zero 2 (hx0 k hk)
  have hprodY : ∏ k ∈ I, Y k = a₆ ^ I.card / ∏ k ∈ I, x k ^ 2 := by
    rw [prod_congr rfl hY, prod_div_distrib, prod_const]
  have hsumY : ∑ k ∈ I, Y k = a₆ * (∑ k ∈ I, (x k)⁻¹) ^ 2 := by
    rw [sum_congr rfl hY, sum_sq_of_two h2, mul_sum]
    exact sum_congr rfl fun k _ => by rw [div_eq_mul_inv, inv_pow]
  have hmixed : ∑ j ∈ I, x j * ∏ i ∈ I.erase j, x i ^ 2
      = (∏ k ∈ I, x k ^ 2) * ∑ k ∈ I, (x k)⁻¹ := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hm : x j ^ 2 * ∏ i ∈ I.erase j, x i ^ 2 = ∏ i ∈ I, x i ^ 2 :=
      mul_prod_erase I (fun i => x i ^ 2) hj
    have hxj := hx0 j hj
    rw [← hm]
    field_simp
  have H1 : (∏ k ∈ I, x k ^ 2) ^ 2 * (1 + ∑ k ∈ I, (x k)⁻¹) = a₆ ^ I.card := by
    rw [hmixed, hprodY, eq_div_iff hP20] at r0
    linear_combination r0
  have H2 : (∑ k ∈ I, x k) ^ 2 + ∑ k ∈ I, x k = a₆ * (∑ k ∈ I, (x k)⁻¹) ^ 2 := by
    rw [← sum_sq_of_two h2 I x, hsumY] at r1
    exact r1
  linear_combination (∏ k ∈ I, x k ^ 2) ^ 4 * H2
    + a₆ * ((∏ k ∈ I, x k ^ 2) ^ 2 * (1 + ∑ k ∈ I, (x k)⁻¹) + a₆ ^ I.card) * H1
    - a₆ * (∏ k ∈ I, x k ^ 2) ^ 4 * (∑ k ∈ I, (x k)⁻¹) * h2

private theorem char_two_chain (h2 : (2 : K) = 0) (ξ : ι → K) (a₆ c : K) (hc : c ^ 2 = a₆)
    (ha₆ : a₆ ≠ 0) (hx0 : ∀ k ∈ I, x k ≠ 0) (hinj : Set.InjOn x I)
    (hξ : ∀ k ∈ I, ξ k = c / x k) (hξx : ∀ k ∈ I, ∀ j ∈ I, ξ k ≠ x j)
    (hvan : ∀ k ∈ I, ξ k + ∑ j ∈ I, (x j / (ξ k - x j) + x j ^ 2 / (ξ k - x j) ^ 2) = 0) :
    (a₆ + ∑ k ∈ I, x k + (∑ k ∈ I, x k) ^ 2) * (∏ k ∈ I, x k ^ 2) ^ 4
      = a₆ ^ (2 * I.card + 1) := by
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ha₆ (by rw [← hc]; ring)
  have hY : ∀ k ∈ I, ξ k ^ 2 = a₆ / x k ^ 2 := fun k hk => by
    rw [hξ k hk, div_pow, hc]
  have hξ0 : ∀ k ∈ I, ξ k ≠ 0 := fun k hk => by
    rw [hξ k hk]
    exact div_ne_zero hc0 (hx0 k hk)
  have hYx : ∀ k ∈ I, ∀ j ∈ I, ξ k ^ 2 - x j ^ 2 ≠ 0 := fun k hk j hj => by
    rw [← sub_sq_of_two h2]
    exact pow_ne_zero 2 (sub_ne_zero.mpr (hξx k hk j hj))
  have hYinj : Set.InjOn (fun k => ξ k ^ 2) I := by
    intro k hk k' hk' hkk
    have hkk' : ξ k ^ 2 = ξ k' ^ 2 := hkk
    have h0 : (ξ k - ξ k') ^ 2 = 0 := by rw [sub_sq_of_two h2, hkk', sub_self]
    have h1 : ξ k = ξ k' := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)
    rw [hξ k hk, hξ k' hk', div_eq_mul_inv, div_eq_mul_inv] at h1
    exact hinj hk hk' (inv_inj.mp (mul_left_cancel₀ hc0 h1))
  have hroot : ∀ k ∈ I, (BtP I x).eval (ξ k ^ 2) = 0 := fun k hk =>
    BtP_eval_eq_zero I x (hYx k hk) (one_add_sum_eq_zero I x h2 (hξ0 k hk) (hξx k hk) (hvan k hk))
  have hBR := BtP_eq_prod I x (fun k => ξ k ^ 2) hI hYinj hroot
  exact close_of_reads I x (fun k => ξ k ^ 2) h2 a₆ hx0 hY (read_zero I x _ h2 hBR)
    (read_pred I x _ h2 hI hBR)

end CharTwoOrdAlgebra

section CharTwoOrdCurve

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

variable {F : Type*} [Field F] [DecidableEq F] {V : WeierstrassCurve F}

omit [DecidableEq F] in

private lemma equation_ord (ha1 : V.a₁ = 1) (ha3 : V.a₃ = 0) (ha4 : V.a₄ = 0) {x y : F}
    (h : V.toAffine.Equation x y) : y ^ 2 + x * y = x ^ 3 + V.a₂ * x ^ 2 + V.a₆ := by
  rw [Affine.equation_iff, ha1, ha3, ha4] at h
  linear_combination h

private lemma addX_twoTorsion (h2 : (2 : F) = 0) (ha1 : V.a₁ = 1) (ha3 : V.a₃ = 0)
    (ha4 : V.a₄ = 0) {c x y : F} (hc : c ^ 2 = V.a₆) (h : V.toAffine.Equation x y)
    (hx : x ≠ 0) :
    V.toAffine.addX 0 x (V.toAffine.slope 0 x c y) = c / x := by
  have e := equation_ord ha1 ha3 ha4 h
  rw [Affine.slope_of_X_ne (Ne.symm hx)]
  simp only [Affine.addX, toAffine, ha1]
  apply mul_left_cancel₀ (pow_ne_zero 2 hx)
  have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  linear_combination e + hc + (V.a₆ - c * (x + y)) * h2
    + ((c - y) ^ 2 * (x * x⁻¹ + 1) - x * (c - y) - c * x) * hinv

omit [DecidableEq F] in

private lemma nonsingular_twoTorsion [V.IsElliptic] (ha3 : V.a₃ = 0) (ha4 : V.a₄ = 0) {c : F}
    (hc : c ^ 2 = V.a₆) : V.toAffine.Nonsingular 0 c := by
  rw [← Affine.equation_iff_nonsingular, Affine.equation_iff, ha3, ha4]
  linear_combination hc

omit [DecidableEq F] in

private lemma negY_twoTorsion (h2 : (2 : F) = 0) (ha3 : V.a₃ = 0) (c : F) :
    V.toAffine.negY 0 c = c := by
  simp only [Affine.negY, ha3]
  linear_combination (-c) * h2

private lemma coordsOrZero_twoTorsion_add_fst (h2 : (2 : F) = 0) (ha1 : V.a₁ = 1)
    (ha3 : V.a₃ = 0) (ha4 : V.a₄ = 0) {c : F} (hT : V.toAffine.Nonsingular 0 c)
    (hc : c ^ 2 = V.a₆) {x y : F} (h : V.toAffine.Nonsingular x y) (hx : x ≠ 0) :
    ((Affine.Point.some 0 c hT + Affine.Point.some x y h).coordsOrZero).1 = c / x := by
  rw [Affine.Point.add_of_X_ne (Ne.symm hx), Affine.Point.coordsOrZero_some]
  exact addX_twoTorsion h2 ha1 ha3 ha4 hc h.1 hx

end CharTwoOrdCurve

section CharTwoOrdCore

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

private theorem char_two_ordinary_core_of {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    (h2 : (2 : K) = 0) (V : WeierstrassCurve K) (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0)
    (ha₄ : V.a₄ = 0) [V.IsElliptic] {n : ℕ} (Q : V.toAffine.Point)
    (hΔ : V.Δ = V.a₆)
    (hrow : (V.veluQuotient (V.oddOrderSummingSet Q n)).Δ *
          (∏ P ∈ V.oddOrderSummingSet Q n, V.veluU P.1 P.2) ^ 4
        = V.Δ ^ (2 * n + 1) ↔
      (V.a₆ + (∑ k ∈ Finset.Icc 1 n, ((k • Q).coordsOrZero).1)
          + (∑ k ∈ Finset.Icc 1 n, ((k • Q).coordsOrZero).1) ^ 2)
        * (∏ k ∈ Finset.Icc 1 n, ((k • Q).coordsOrZero).1 ^ 2) ^ 4
      = V.a₆ ^ (2 * (Finset.Icc 1 n).card + 1))
    (xv : K → K)
    (hxv : ∀ v, xv v = v + ∑ k ∈ Finset.Icc 1 n,
      (((k • Q).coordsOrZero).1 / (v - ((k • Q).coordsOrZero).1)
        + ((k • Q).coordsOrZero).1 ^ 2 / (v - ((k • Q).coordsOrZero).1) ^ 2))
    (hx0 : ∀ k ∈ Finset.Icc 1 n, ((k • Q).coordsOrZero).1 ≠ 0)
    (hinj : Set.InjOn (fun k : ℕ => ((k • Q).coordsOrZero).1) (Finset.Icc 1 n))
    (hne : ∀ T : V.toAffine.Point, T ≠ 0 → (2 : ℕ) • T = 0 → ∀ (j : ℕ) {k : ℕ}, 1 ≤ k → k ≤ n →
      ((T + j • Q).coordsOrZero).1 ≠ ((k • Q).coordsOrZero).1)
    (hcoset : ∀ T : V.toAffine.Point, T ≠ 0 → (2 : ℕ) • T = 0 → ∀ m : ℕ,
      xv ((T + m • Q).coordsOrZero).1 = xv (T.coordsOrZero).1) :
    (V.veluQuotient (V.oddOrderSummingSet Q n)).Δ *
        (∏ P ∈ V.oddOrderSummingSet Q n, V.veluU P.1 P.2) ^ 4
      = V.Δ ^ (2 * n + 1) := by
  obtain ⟨c, hc'⟩ := IsAlgClosed.exists_eq_mul_self V.a₆
  have hc : c ^ 2 = V.a₆ := (sq c).trans hc'.symm
  have ha₆ : V.a₆ ≠ 0 := hΔ ▸ V.isUnit_Δ.ne_zero
  have hT : V.toAffine.Nonsingular 0 c := nonsingular_twoTorsion ha₃ ha₄ hc
  have hT0 : (Affine.Point.some 0 c hT : V.toAffine.Point) ≠ 0 := Affine.Point.some_ne_zero hT
  have hT2 : (2 : ℕ) • (Affine.Point.some 0 c hT : V.toAffine.Point) = 0 := by
    rw [two_nsmul]
    exact Affine.Point.add_self_of_Y_eq (negY_twoTorsion h2 ha₃ c).symm
  have hξ : ∀ k ∈ Finset.Icc 1 n, ((Affine.Point.some 0 c hT + k • Q).coordsOrZero).1
      = c / ((k • Q).coordsOrZero).1 := by
    intro k hk
    have hxk := hx0 k hk
    rcases hP : k • Q with _ | ⟨xk, yk, hk'⟩
    · rw [hP, Affine.Point.coordsOrZero_zero] at hxk
      exact absurd rfl hxk
    · rw [hP, Affine.Point.coordsOrZero_some] at hxk
      rw [Affine.Point.coordsOrZero_some]
      exact coordsOrZero_twoTorsion_add_fst h2 ha₁ ha₃ ha₄ hT hc hk' hxk
  have hxv0 : xv 0 = 0 := by
    rw [hxv, zero_add]
    exact Finset.sum_eq_zero fun k _ => by field_simp; ring
  have hvan : ∀ k ∈ Finset.Icc 1 n, ((Affine.Point.some 0 c hT + k • Q).coordsOrZero).1
      + ∑ j ∈ Finset.Icc 1 n,
        (((j • Q).coordsOrZero).1 / (((Affine.Point.some 0 c hT + k • Q).coordsOrZero).1
            - ((j • Q).coordsOrZero).1)
          + ((j • Q).coordsOrZero).1 ^ 2 / (((Affine.Point.some 0 c hT + k • Q).coordsOrZero).1
            - ((j • Q).coordsOrZero).1) ^ 2) = 0 := by
    intro k _
    have h1 := hcoset (Affine.Point.some 0 c hT) hT0 hT2 k
    rw [Affine.Point.coordsOrZero_some, hxv0, hxv] at h1
    exact h1
  have hξx : ∀ k ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n,
      ((Affine.Point.some 0 c hT + k • Q).coordsOrZero).1 ≠ ((j • Q).coordsOrZero).1 :=
    fun k _ j hj => hne _ hT0 hT2 k (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  have key := char_two_chain (Finset.Icc 1 n) (fun k => ((k • Q).coordsOrZero).1) h2
    (fun k => ((Affine.Point.some 0 c hT + k • Q).coordsOrZero).1) V.a₆ c hc ha₆ hx0 hinj
    hξ hξx hvan
  exact hrow.mpr key

end CharTwoOrdCore

end N5IDAux1

namespace N5IDAux4

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

section TraceTwins

variable {V : WeierstrassCurve F} {Q : V.toAffine.Point} {n : ℕ}

private lemma xvSum_eq_orbitTrace' (hQ : addOrderOf Q = 2 * n + 1) {xP yP : F}
    (hns : V.toAffine.Nonsingular xP yP)
    (hx : ∀ k, 1 ≤ k → k ≤ n → xP ≠ ((k • Q).coordsOrZero).1) :
    xvSum V Q n xP
      = orbitTrace V Q n (Affine.Point.some xP yP hns)
        - 2 * ∑ k ∈ Finset.Icc 1 n, ((k • Q).coordsOrZero).1 := by
  rw [orbitTrace_fold hQ]
  have hper : ∀ k ∈ Finset.Icc 1 n,
      ((Affine.Point.some xP yP hns + k • Q).coordsOrZero).1
        + ((Affine.Point.some xP yP hns - k • Q).coordsOrZero).1
      = 2 * ((k • Q).coordsOrZero).1
        + (V.veluT ((k • Q).coordsOrZero).1 ((k • Q).coordsOrZero).2
            / (xP - ((k • Q).coordsOrZero).1)
          + V.veluU ((k • Q).coordsOrZero).1 ((k • Q).coordsOrZero).2
            / (xP - ((k • Q).coordsOrZero).1) ^ 2) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    obtain ⟨xk, yk, hknd, hkeq, hkc⟩ :=
      exists_some_of_ne_zero (nsmul_ne_zero hQ hk.1 (by omega))
    have hxk : xP ≠ xk := by
      have := hx k hk.1 hk.2
      rwa [hkc] at this
    have hadd : Affine.Point.some xP yP hns + k • Q
        = Affine.Point.some _ _ (Affine.nonsingular_add hns hknd
            (fun hxy => absurd hxy.1 hxk)) := by
      rw [hkeq]
      exact Affine.Point.add_some (fun hxy => absurd hxy.1 hxk)
    have hneg : -(k • Q) = Affine.Point.some xk (V.toAffine.negY xk yk)
        ((Affine.nonsingular_neg ..).mpr hknd) := by
      rw [hkeq, Affine.Point.neg_some]
    have hsub : Affine.Point.some xP yP hns - k • Q
        = Affine.Point.some _ _ (Affine.nonsingular_add hns
            ((Affine.nonsingular_neg ..).mpr hknd) (fun hxy => absurd hxy.1 hxk)) := by
      rw [sub_eq_add_neg, hneg]
      exact Affine.Point.add_some (fun hxy => absurd hxy.1 hxk)
    rw [hadd, hsub, hkc]
    simp only [Affine.Point.coordsOrZero_some]
    linear_combination chord_sum' V hns.1 hknd.1 hxk
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, Finset.mul_sum, xvSum]
  simp only [Affine.Point.coordsOrZero_some]
  ring

private theorem xvSum_orbit_const' (hQ : addOrderOf Q = 2 * n + 1) {P : V.toAffine.Point}
    (haff : ∀ j : ℕ, P + j • Q ≠ 0)
    (hx : ∀ j : ℕ, ∀ k, 1 ≤ k → k ≤ n →
      ((P + j • Q).coordsOrZero).1 ≠ ((k • Q).coordsOrZero).1) (m : ℕ) :
    xvSum V Q n (((P + m • Q).coordsOrZero).1) = xvSum V Q n ((P.coordsOrZero).1) := by
  obtain ⟨xP, yP, hPns, hPeq, hPc⟩ := exists_some_of_ne_zero
    (by simpa using haff 0)
  obtain ⟨xM, yM, hMns, hMeq, hMc⟩ := exists_some_of_ne_zero (haff m)
  have hxP : ∀ k, 1 ≤ k → k ≤ n → xP ≠ ((k • Q).coordsOrZero).1 := by
    intro k h1 h2
    have := hx 0 k h1 h2
    rwa [zero_nsmul, add_zero, hPeq, Affine.Point.coordsOrZero_some] at this
  have hxM : ∀ k, 1 ≤ k → k ≤ n → xM ≠ ((k • Q).coordsOrZero).1 := by
    intro k h1 h2
    have := hx m k h1 h2
    rwa [hMeq, Affine.Point.coordsOrZero_some] at this
  have e1 := xvSum_eq_orbitTrace' hQ hPns hxP
  have e2 := xvSum_eq_orbitTrace' hQ hMns hxM
  have htr : orbitTrace V Q n (Affine.Point.some xM yM hMns)
      = orbitTrace V Q n (Affine.Point.some xP yP hPns) := by
    rw [← hMeq, ← hPeq]
    have h0 : P = P + (0 : ℕ) • Q := by rw [zero_nsmul, add_zero]
    rw [orbitTrace_add_smul hQ P m]
  rw [hMc, hPc]
  rw [e1, e2, htr]

end TraceTwins

section CosetFacts

variable {V : WeierstrassCurve F} {Q : V.toAffine.Point} {n : ℕ}

private lemma two_torsion_ne_nsmul (hQ : addOrderOf Q = 2 * n + 1) {T : V.toAffine.Point}
    (hT0 : T ≠ 0) (hT2 : (2 : ℕ) • T = 0) (m : ℕ) : T ≠ m • Q := by
  intro hTm
  apply hT0
  have h1 : (2 * n + 1) • T = 0 := by
    rw [hTm, ← mul_nsmul', mul_comm, mul_nsmul', ← hQ, addOrderOf_nsmul_eq_zero, nsmul_zero]
  have h2 : (2 * n + 1 + 1) • T = 0 := by
    have he : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
    rw [he, mul_comm, mul_nsmul', hT2, nsmul_zero]
  rw [succ_nsmul, h1, zero_add] at h2
  exact h2

private lemma coset_rel_nsmul (hQ : addOrderOf Q = 2 * n + 1) {T : V.toAffine.Point}
    (i c : ℕ) (h : T + i • Q = c • Q) :
    T = (c + (2 * n + 1 - i % (2 * n + 1))) • Q := by
  have hmod : (i % (2 * n + 1)) • Q = i • Q := by
    rw [← hQ]
    exact mod_addOrderOf_nsmul Q i
  have hlt : i % (2 * n + 1) < 2 * n + 1 := Nat.mod_lt _ (by omega)
  have key : T + (i % (2 * n + 1)) • Q = c • Q := by rw [hmod]; exact h
  have hNQ : (2 * n + 1) • Q = 0 := by
    rw [← hQ]
    exact addOrderOf_nsmul_eq_zero Q
  have hsum : T + ((i % (2 * n + 1)) + (2 * n + 1 - i % (2 * n + 1))) • Q
      = (c + (2 * n + 1 - i % (2 * n + 1))) • Q := by
    rw [add_nsmul, ← add_assoc, key, ← add_nsmul]
  rwa [Nat.add_sub_cancel' (le_of_lt hlt), hNQ, add_zero] at hsum

private lemma coset_add_nsmul_ne_zero (hQ : addOrderOf Q = 2 * n + 1) {T : V.toAffine.Point}
    (hT0 : T ≠ 0) (hT2 : (2 : ℕ) • T = 0) (j : ℕ) : T + j • Q ≠ 0 := by
  intro h
  exact two_torsion_ne_nsmul hQ hT0 hT2 _
    (coset_rel_nsmul hQ j 0 (by rw [h, zero_nsmul]))

private lemma coset_xco_ne_kernel (hQ : addOrderOf Q = 2 * n + 1) {T : V.toAffine.Point}
    (hT0 : T ≠ 0) (hT2 : (2 : ℕ) • T = 0) (j : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ((T + j • Q).coordsOrZero).1 ≠ ((k • Q).coordsOrZero).1 := by
  intro heq
  have hTj : T + j • Q ≠ 0 := coset_add_nsmul_ne_zero hQ hT0 hT2 j
  have hkQ : k • Q ≠ 0 := nsmul_ne_zero hQ hk1 (by omega)
  obtain ⟨x, y, h, hPeq, hPc⟩ := exists_some_of_ne_zero hTj
  obtain ⟨x', y', h', hkeq, hkc⟩ := exists_some_of_ne_zero hkQ
  have hxx : x = x' := by
    have e1 : ((T + j • Q).coordsOrZero).1 = x := by rw [hPc]
    have e2 : ((k • Q).coordsOrZero).1 = x' := by rw [hkc]
    rw [e1, e2] at heq
    exact heq
  rcases (Affine.Point.X_eq_iff (h₁ := h) (h₂ := h')).mp hxx with hc | hc
  · refine two_torsion_ne_nsmul hQ hT0 hT2 _ (coset_rel_nsmul hQ j k ?_)
    rw [hPeq, hkeq, hc]
  · refine two_torsion_ne_nsmul hQ hT0 hT2 _ (coset_rel_nsmul hQ (j + k) 0 ?_)
    have h1 : T + j • Q = -(k • Q) := by rw [hPeq, hkeq, hc]
    rw [zero_nsmul, add_nsmul, ← add_assoc, h1, neg_add_cancel]

private lemma xco_nsmul_injOn (hQ : addOrderOf Q = 2 * n + 1) :
    Set.InjOn (fun k : ℕ => ((k • Q).coordsOrZero).1) (Finset.Icc 1 n : Finset ℕ) := by
  intro k hk k' hk' heq
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
  obtain ⟨x, y, h, hkeq, hkc⟩ := exists_some_of_ne_zero (nsmul_ne_zero hQ hk.1 (by omega))
  obtain ⟨x', y', h', hk'eq, hk'c⟩ := exists_some_of_ne_zero (nsmul_ne_zero hQ hk'.1 (by omega))
  have heq' : ((k • Q).coordsOrZero).1 = ((k' • Q).coordsOrZero).1 := heq
  have hxx : x = x' := by
    have e1 : ((k • Q).coordsOrZero).1 = x := by rw [hkc]
    have e2 : ((k' • Q).coordsOrZero).1 = x' := by rw [hk'c]
    rw [e1, e2] at heq'
    exact heq'
  exact nsmul_injOn_Icc hQ hk.1 hk.2 hk'.1 hk'.2
    (nsmul_eq_of_x_eq hQ hk.1 hk.2 hk'.1 hk'.2 hkeq hk'eq hxx)

private theorem xvSum_coset (hQ : addOrderOf Q = 2 * n + 1) {T : V.toAffine.Point}
    (hT0 : T ≠ 0) (hT2 : (2 : ℕ) • T = 0) (m : ℕ) :
    xvSum V Q n (((T + m • Q).coordsOrZero).1) = xvSum V Q n ((T.coordsOrZero).1) :=
  xvSum_orbit_const' hQ (coset_add_nsmul_ne_zero hQ hT0 hT2)
    (fun j _ hk1 hkn => coset_xco_ne_kernel hQ hT0 hT2 j hk1 hkn) m

end CosetFacts

end N5IDAux4

namespace N5IDChar2

section Invariants

variable {F : Type*} [Field F] (h2 : (2 : F) = 0) (V : WeierstrassCurve F)
  (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0) (ha₄ : V.a₄ = 0)

include h2 ha₁ in

private theorem b₂_V : V.b₂ = 1 := by
  rw [b₂, ha₁]; linear_combination 2 * V.a₂ * h2

include ha₁ ha₃ ha₄ in

private theorem b₄_V : V.b₄ = 0 := by
  rw [b₄, ha₁, ha₃, ha₄]; ring

include h2 ha₃ in

private theorem b₆_V : V.b₆ = 0 := by
  rw [b₆, ha₃]; linear_combination 2 * V.a₆ * h2

include h2 ha₁ ha₃ in

private theorem Δ_of_a₁_one_a₃_zero : V.Δ = V.a₆ + V.a₄ ^ 2 := by
  rw [Δ, b₂, b₄, b₆, b₈, ha₁, ha₃]
  linear_combination (-216 * V.a₆ ^ 2 - 32 * V.a₄ ^ 3 + 144 * V.a₂ * V.a₄ * V.a₆
    + 8 * V.a₂ ^ 2 * V.a₄ ^ 2 - 32 * V.a₂ ^ 3 * V.a₆ - 6 * V.a₂ * V.a₆ - V.a₆
    - 24 * V.a₂ ^ 2 * V.a₆ + 4 * V.a₂ * V.a₄ ^ 2 + 36 * V.a₄ * V.a₆) * h2

include h2 ha₁ ha₃ ha₄ in

private theorem Δ_V : V.Δ = V.a₆ := by
  rw [Δ_of_a₁_one_a₃_zero h2 V ha₁ ha₃, ha₄]; ring

end Invariants

section PerPoint

variable {F : Type*} [Field F] (h2 : (2 : F) = 0) (V : WeierstrassCurve F)
  (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0) (ha₄ : V.a₄ = 0)

include h2 ha₁ ha₃ ha₄ in

private theorem veluT_V (x y : F) : V.veluT x y = x := by
  rw [veluT_eq, b₂_V h2 V ha₁, b₄_V V ha₁ ha₃ ha₄]
  linear_combination (3 : F) * x ^ 2 * h2

include h2 ha₁ ha₃ ha₄ in

private theorem veluU_V {x y : F} (heq : V.toAffine.Equation x y) : V.veluU x y = x ^ 2 := by
  rw [V.veluU_eq_Ψ₂Sq_eval heq, Ψ₂Sq, b₂_V h2 V ha₁, b₄_V V ha₁ ha₃ ha₄, b₆_V h2 V ha₃]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  linear_combination (2 : F) * x ^ 3 * h2

include h2 ha₁ ha₃ ha₄ in

private theorem veluW_V {x y : F} (heq : V.toAffine.Equation x y) : V.veluW x y = 0 := by
  rw [veluW, veluU_V h2 V ha₁ ha₃ ha₄ heq, veluT_V h2 V ha₁ ha₃ ha₄]
  linear_combination (x : F) ^ 2 * h2

include h2 ha₁ ha₃ in

private theorem veluGy_V (x y : F) : V.veluGy x y = x := by
  simp only [veluGy, ha₁, ha₃]
  linear_combination (-y - x) * h2

end PerPoint

section Sums

variable {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) = 0) (V : WeierstrassCurve F)
  (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0) (ha₄ : V.a₄ = 0)

omit [DecidableEq F] in
include h2 ha₁ ha₃ ha₄ in

private theorem veluTSum_V (S : Finset (F × F)) :
    V.veluTSum S = ∑ P ∈ S, P.1 := by
  unfold veluTSum
  exact Finset.sum_congr rfl fun P _ => veluT_V h2 V ha₁ ha₃ ha₄ P.1 P.2

omit [DecidableEq F] in
include h2 ha₁ ha₃ ha₄ in

private theorem veluWSum_V (S : Finset (F × F)) (hS : ∀ P ∈ S, V.toAffine.Equation P.1 P.2) :
    V.veluWSum S = 0 := by
  unfold veluWSum
  exact Finset.sum_eq_zero fun P hP => veluW_V h2 V ha₁ ha₃ ha₄ (hS P hP)

omit [DecidableEq F] in
include h2 ha₁ ha₃ ha₄ in

private theorem prod_veluU_V (S : Finset (F × F)) (hS : ∀ P ∈ S, V.toAffine.Equation P.1 P.2) :
    ∏ P ∈ S, V.veluU P.1 P.2 = (∏ P ∈ S, P.1) ^ 2 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun P hP => veluU_V h2 V ha₁ ha₃ ha₄ (hS P hP)

end Sums

section QuotientΔ

variable {F : Type*} [Field F] (h2 : (2 : F) = 0) (V : WeierstrassCurve F)
  (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0) (ha₄ : V.a₄ = 0)

include h2 ha₁ ha₃ ha₄ in

private theorem veluQuotient_coeffs (S : Finset (F × F))
    (hW : V.veluWSum S = 0) :
    (V.veluQuotient S).a₁ = 1 ∧ (V.veluQuotient S).a₃ = 0 ∧
    (V.veluQuotient S).a₄ = V.veluTSum S ∧
    (V.veluQuotient S).a₆ = V.a₆ + V.veluTSum S := by
  refine ⟨by rw [veluQuotient_a₁, ha₁], by rw [veluQuotient_a₃, ha₃], ?_, ?_⟩
  · rw [veluQuotient_a₄, ha₄]
    linear_combination (-(3 : F)) * V.veluTSum S * h2
  · rw [veluQuotient_a₆, hW, b₂_V h2 V ha₁]
    linear_combination (-V.veluTSum S) * h2

include h2 ha₁ ha₃ ha₄ in

private theorem Δ_veluQuotient_V (S : Finset (F × F))
    (hS : ∀ P ∈ S, V.toAffine.Equation P.1 P.2) :
    (V.veluQuotient S).Δ = V.a₆ + (∑ P ∈ S, P.1) + (∑ P ∈ S, P.1) ^ 2 := by
  set t := ∑ P ∈ S, P.1 with ht
  have hW := veluWSum_V h2 V ha₁ ha₃ ha₄ S hS
  have hT := veluTSum_V h2 V ha₁ ha₃ ha₄ S
  obtain ⟨h1, h3, h4, h6⟩ := veluQuotient_coeffs h2 V ha₁ ha₃ ha₄ S hW
  rw [hT] at h4 h6
  rw [Δ_of_a₁_one_a₃_zero h2 (V.veluQuotient S) h1 h3, h4, h6, ← ht]

end QuotientΔ

section VGlue

open N5IDAux4

variable {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) = 0) (V : WeierstrassCurve F)
  (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0) (ha₄ : V.a₄ = 0)
  {n : ℕ} {Q : V.toAffine.Point} (hQ : addOrderOf Q = 2 * n + 1)

include hQ in

private theorem kQ_equation {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    V.toAffine.Equation ((k • Q).coordsOrZero).1 ((k • Q).coordsOrZero).2 := by
  obtain ⟨_, _, hnd, _, hc⟩ := exists_some_of_ne_zero (nsmul_ne_zero hQ hk1 (by omega))
  rw [hc]
  exact hnd.1

include h2 ha₁ ha₃ hQ in

private theorem xk_ne_zero {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ((k • Q).coordsOrZero).1 ≠ 0 := by
  obtain ⟨xk, yk, hnd, heq, hc⟩ :=
    exists_some_of_ne_zero (nsmul_ne_zero hQ hk1 (by omega))
  rw [hc]
  have h2t : (2 : ℕ) • (k • Q) ≠ 0 := two_nsmul_nsmul_ne_zero hQ hk1 hkn
  rw [heq] at h2t
  have := veluGy_ne_zero_of_two_nsmul_ne_zero hnd h2t
  rwa [veluGy_V h2 V ha₁ ha₃] at this

include h2 ha₁ ha₃ ha₄ hQ in

private theorem xvSum_V (v : F) :
    xvSum V Q n v = v + ∑ k ∈ Finset.Icc 1 n,
      (((k • Q).coordsOrZero).1 / (v - ((k • Q).coordsOrZero).1)
        + ((k • Q).coordsOrZero).1 ^ 2 / (v - ((k • Q).coordsOrZero).1) ^ 2) := by
  unfold N5IDAux4.xvSum
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  rw [veluT_V h2 V ha₁ ha₃ ha₄, veluU_V h2 V ha₁ ha₃ ha₄ (kQ_equation V hQ hk.1 hk.2)]

include h2 ha₁ ha₃ ha₄ hQ in

private theorem row_iff_chain :
    (V.veluQuotient (V.oddOrderSummingSet Q n)).Δ *
        (∏ P ∈ V.oddOrderSummingSet Q n, V.veluU P.1 P.2) ^ 4
      = V.Δ ^ (2 * n + 1) ↔
    (V.a₆ + (∑ k ∈ Finset.Icc 1 n, ((k • Q).coordsOrZero).1)
        + (∑ k ∈ Finset.Icc 1 n, ((k • Q).coordsOrZero).1) ^ 2)
      * (∏ k ∈ Finset.Icc 1 n, ((k • Q).coordsOrZero).1 ^ 2) ^ 4
    = V.a₆ ^ (2 * (Finset.Icc 1 n).card + 1) := by
  have hS : ∀ P ∈ V.oddOrderSummingSet Q n, V.toAffine.Equation P.1 P.2 :=
    (isOddVeluSet_oddOrderSummingSet' hQ).1
  rw [Δ_veluQuotient_V h2 V ha₁ ha₃ ha₄ _ hS,
    prod_veluU_V h2 V ha₁ ha₃ ha₄ _ hS, Δ_V h2 V ha₁ ha₃ ha₄,
    sum_oddOrderSummingSet_eq hQ (fun P => P.1),
    prod_oddOrderSummingSet_eq hQ (fun P => P.1),
    Nat.card_Icc, Nat.add_sub_cancel, ← Finset.prod_pow]

end VGlue

end N5IDChar2

open Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine toCharNeTwoNF isUnit_Δ b₄_of_isCharNeTwoNF Affine.negY a₁_of_isCharNeTwoNF Affine.slope_of_X_ne a₃ map_map a₁ twoTorsionPolynomial_discr map b₂ twoTorsionPolynomial variableChange_a₃ isElliptic_iff mk Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Δ_of_char_two Affine.Point.X_eq_iff variableChange_a₆ Affine.Point.add_self_of_Y_eq toCharNeTwoNF_spec IsCharNeTwoNF variableChange_Δ b₆_of_isCharNeTwoNF variableChange_a₂ Affine.nonsingular_add map_id a₃_of_isCharNeTwoNF toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Ψ₂Sq_eq Affine.Point.map b₆ b₈ variableChange_a₁ map_a₁ Affine.equation_iff_nonsingular b₂_of_isCharNeTwoNF Affine.Point.some_ne_zero variableChange_a₄ Δ VariableChange Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne j b₄ Δ' map_a₃ veluGx veluGy veluT veluU veluW veluT_eq veluU_eq_Ψ₂Sq_eval veluTSum veluWSum veluQuotient veluQuotient_a₁ veluQuotient_a₂ veluQuotient_a₃ veluQuotient_a₄ veluQuotient_a₆ veluQuotient_b₂ veluQuotient_b₄ veluQuotient_b₆ Affine.Point.coordsOrZero Affine.Point.coordsOrZero_zero Affine.Point.coordsOrZero_some oddOrderSummingSet mem_oddOrderSummingSet IsOddVeluSet veluX vcInvEmbedding vcInvEmbedding_apply variableChange_veluU variableChange_veluTSum variableChange_veluWSum map_veluU map_veluQuotient"
p2m_open "WeierstrassCurve"

section VarChangeQuotient

variable {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K)
  (S : Finset (K × K))

private theorem variableChange_veluQuotient :
    (C • W).veluQuotient (S.map (vcInvEmbedding C)) = C • W.veluQuotient S := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hT := variableChange_veluTSum C W S
  have hW := variableChange_veluWSum C W S
  ext
  · simp only [veluQuotient_a₁, variableChange_a₁]
  · simp only [veluQuotient_a₁, veluQuotient_a₂, variableChange_a₂]
  · simp only [veluQuotient_a₁, veluQuotient_a₃, variableChange_a₃]
  · simp only [veluQuotient_a₄, variableChange_a₄, veluQuotient_a₁, veluQuotient_a₂,
      veluQuotient_a₃, hT, Units.val_inv_eq_inv_val]
    field_simp
    ring
  · simp only [veluQuotient_a₆, variableChange_a₆, veluQuotient_a₁, veluQuotient_a₂,
      veluQuotient_a₃, veluQuotient_a₄, hT, hW, b₂, variableChange_a₁, variableChange_a₂,
      Units.val_inv_eq_inv_val]
    field_simp
    ring

private theorem variableChange_veluQuotient_Δ :
    ((C • W).veluQuotient (S.map (vcInvEmbedding C))).Δ
      = ((C.u⁻¹ : Kˣ) : K) ^ 12 * (W.veluQuotient S).Δ := by
  rw [variableChange_veluQuotient, variableChange_Δ]

end VarChangeQuotient

section VarChangeProdU

variable {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K)
  (S : Finset (K × K))

private theorem variableChange_prod_veluU :
    ∏ P ∈ S.map (vcInvEmbedding C), (C • W).veluU P.1 P.2
      = ((C.u⁻¹ : Kˣ) : K) ^ (6 * S.card) * ∏ P ∈ S, W.veluU P.1 P.2 := by
  rw [Finset.prod_map, pow_mul, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun P _ => by
    simpa only [vcInvEmbedding_apply] using variableChange_veluU C W P.1 P.2

end VarChangeProdU

section IdentityTransport

variable {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K)
  (S : Finset (K × K)) (n : ℕ)

private theorem identity_variableChange_iff (hcard : S.card = n) :
    ((C • W).veluQuotient (S.map (vcInvEmbedding C))).Δ *
        (∏ P ∈ S.map (vcInvEmbedding C), (C • W).veluU P.1 P.2) ^ 4
      = (C • W).Δ ^ (2 * n + 1) ↔
    (W.veluQuotient S).Δ * (∏ P ∈ S, W.veluU P.1 P.2) ^ 4 = W.Δ ^ (2 * n + 1) := by
  have hu' : ((C.u⁻¹ : Kˣ) : K) ≠ 0 := C.u⁻¹.ne_zero
  have hfac : ((C.u⁻¹ : Kˣ) : K) ^ (12 * (2 * n + 1)) ≠ 0 := pow_ne_zero _ hu'
  rw [variableChange_veluQuotient_Δ, variableChange_prod_veluU, variableChange_Δ, hcard]
  rw [show ((C.u⁻¹ : Kˣ) : K) ^ 12 * (W.veluQuotient S).Δ *
        (((C.u⁻¹ : Kˣ) : K) ^ (6 * n) * ∏ P ∈ S, W.veluU P.1 P.2) ^ 4
      = ((C.u⁻¹ : Kˣ) : K) ^ (12 * (2 * n + 1)) *
        ((W.veluQuotient S).Δ * (∏ P ∈ S, W.veluU P.1 P.2) ^ 4) from by ring,
     show (((C.u⁻¹ : Kˣ) : K) ^ 12 * W.Δ) ^ (2 * n + 1)
      = ((C.u⁻¹ : Kˣ) : K) ^ (12 * (2 * n + 1)) * W.Δ ^ (2 * n + 1) from by ring]
  exact mul_right_inj' hfac

end IdentityTransport

namespace Affine
p2m_export "WeierstrassCurve.Affine" "map_slope Equation negY slope_of_X_ne map_a₃ slope map Point.some Point.X_eq_iff Nonsingular Point.add_self_of_Y_eq negAddY map_addY map_addX nonsingular_add slope_of_Y_ne Point addX map_a₁ Point.add_some nonsingular_neg Point.map equation_iff_nonsingular Point.some_ne_zero map_negY addY Y_eq_of_X_eq Point.add_of_X_ne equation_iff map_nonsingular polynomial Point.neg_some Point.add_self_of_Y_ne Point.coordsOrZero Point.coordsOrZero_zero Point.coordsOrZero_some vcX vcY vcXInv vcYInv vcXInv_vcX vcYInv_vcY"
p2m_open "WeierstrassCurve.Affine"

section VCFormulas

variable {K : Type*} [Field K] {C : VariableChange K} {W : WeierstrassCurve.Affine K}

private lemma vc_u_ne_zero : (C.u : K) ≠ 0 := C.u.ne_zero

private lemma vcX_injective : Function.Injective (vcX C) := fun x₁ x₂ h => by
  have := congrArg (vcXInv C) h
  simpa only [vcXInv_vcX] using this

private lemma vcY_injective (x' : K) : Function.Injective (vcY C x') := fun y₁ y₂ h => by
  have := congrArg (vcYInv C (vcX C x')) h
  simpa only [vcYInv_vcY] using this

private lemma negY_variableChange (x' y' : K) :
    W.negY (vcX C x') (vcY C x' y') = vcY C x' ((C • W).toAffine.negY x' y') := by
  have hu : (C.u : K) ≠ 0 := vc_u_ne_zero
  simp only [negY, vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma Yeq_variableChange_iff (x₁' x₂' y₁' y₂' : K) :
    (vcX C x₁' = vcX C x₂' ∧ vcY C x₁' y₁' = W.negY (vcX C x₂') (vcY C x₂' y₂'))
      ↔ x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂' := by
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : x₁' = x₂' := vcX_injective hx
    subst hx'
    refine ⟨rfl, ?_⟩
    rw [negY_variableChange x₁' y₂'] at hy
    exact vcY_injective x₁' hy
  · rintro ⟨hx, hy⟩
    subst hx
    exact ⟨rfl, by rw [negY_variableChange x₁' y₂', hy]⟩

private lemma addX_variableChange (x₁' x₂' ℓ : K) :
    W.addX (vcX C x₁') (vcX C x₂') ((C.u : K) * ℓ + C.s)
      = vcX C ((C • W).toAffine.addX x₁' x₂' ℓ) := by
  have hu : (C.u : K) ≠ 0 := vc_u_ne_zero
  simp only [addX, vcX, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  field_simp
  ring

private lemma addY_variableChange (x₁' x₂' y₁' ℓ : K) :
    W.addY (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') ((C.u : K) * ℓ + C.s)
      = vcY C ((C • W).toAffine.addX x₁' x₂' ℓ) ((C • W).toAffine.addY x₁' x₂' y₁' ℓ) := by
  have hu : (C.u : K) ≠ 0 := vc_u_ne_zero
  simp only [addY, negAddY, addX, negY, vcX, vcY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

variable [DecidableEq K]

private lemma slope_variableChange (x₁' x₂' y₁' y₂' : K)
    (h₁ : (C • W).toAffine.Equation x₁' y₁') (h₂ : (C • W).toAffine.Equation x₂' y₂')
    (hxy : ¬(x₁' = x₂' ∧ y₁' = (C • W).toAffine.negY x₂' y₂')) :
    W.slope (vcX C x₁') (vcX C x₂') (vcY C x₁' y₁') (vcY C x₂' y₂')
      = (C.u : K) * (C • W).toAffine.slope x₁' x₂' y₁' y₂' + C.s := by
  have hu : (C.u : K) ≠ 0 := vc_u_ne_zero
  by_cases hx : x₁' = x₂'
  · have hy : y₁' ≠ (C • W).toAffine.negY x₂' y₂' := fun h => hxy ⟨hx, h⟩
    have hyy : y₁' = y₂' := (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy
    subst hx
    subst hyy
    have hyW : vcY C x₁' y₁' ≠ W.negY (vcX C x₁') (vcY C x₁' y₁') := by
      intro h
      exact hy ((Yeq_variableChange_iff x₁' x₁' y₁' y₁').mp ⟨rfl, h⟩).2
    rw [slope_of_Y_ne rfl hyW, slope_of_Y_ne rfl hy]
    have hden' : y₁' - (C • W).toAffine.negY x₁' y₁' ≠ 0 := sub_ne_zero_of_ne hy
    have hd : vcY C x₁' y₁' - W.negY (vcX C x₁') (vcY C x₁' y₁')
        = (C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁') := by
      rw [negY_variableChange x₁' y₁']
      simp only [vcY]; ring
    have hn : 3 * vcX C x₁' ^ 2 + 2 * W.a₂ * vcX C x₁' + W.a₄ - W.a₁ * vcY C x₁' y₁'
        = (C.u : K) ^ 4 * (3 * x₁' ^ 2 + 2 * (C • W).a₂ * x₁'
            + (C • W).a₄ - (C • W).a₁ * y₁')
          + C.s * ((C.u : K) ^ 3 * (y₁' - (C • W).toAffine.negY x₁' y₁')) := by
      simp only [vcX, vcY, negY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
        variableChange_a₄, Units.val_inv_eq_inv_val]
      field_simp
      ring
    rw [hd, hn]
    field_simp
  · have hxW : vcX C x₁' ≠ vcX C x₂' := fun h => hx (vcX_injective h)
    rw [slope_of_X_ne hxW, slope_of_X_ne hx]
    have hd : vcX C x₁' - vcX C x₂' = (C.u : K) ^ 2 * (x₁' - x₂') := by
      simp only [vcX]; ring
    have hn : vcY C x₁' y₁' - vcY C x₂' y₂'
        = (C.u : K) ^ 3 * (y₁' - y₂') + (C.u : K) ^ 2 * C.s * (x₁' - x₂') := by
      simp only [vcY]; ring
    rw [hd, hn]
    have hxne : x₁' - x₂' ≠ 0 := sub_ne_zero_of_ne hx
    field_simp

end VCFormulas

namespace Point
p2m_export "WeierstrassCurve.Affine.Point" "add_of_Y_eq map_id map_map some some.injEq neg_zero X_eq_iff add_self_of_Y_eq map_zero add_some map some_ne_zero add_of_X_ne zero neg_some add_self_of_Y_ne mk coordsOrZero coordsOrZero_zero coordsOrZero_some vcFun vcInvFun variableChangeEquiv"
p2m_open "WeierstrassCurve.Affine.Point"

variable {K : Type*} [Field K] [DecidableEq K] {C : VariableChange K}
  {W : WeierstrassCurve.Affine K}

omit [DecidableEq K] in
private lemma some_eq_some' {W' : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by subst hx hy; rfl

private lemma vcFun_add (P Q : (C • W).toAffine.Point) :
    vcFun C W (P + Q) = vcFun C W P + vcFun C W Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · rw [add_of_Y_eq hxy.1 hxy.2]
    have hxyW := (Yeq_variableChange_iff (W := W) x₁ x₂ y₁ y₂).mpr hxy
    exact (add_of_Y_eq hxyW.1 hxyW.2).symm
  · have hxyW : ¬(vcX C x₁ = vcX C x₂ ∧ vcY C x₁ y₁ = W.negY (vcX C x₂) (vcY C x₂ y₂)) :=
      fun h => hxy ((Yeq_variableChange_iff x₁ x₂ y₁ y₂).mp h)
    have hslope := slope_variableChange (W := W) x₁ x₂ y₁ y₂ h₁.1 h₂.1 hxy
    rw [add_some hxy, show vcFun C W (some _ _ h₁) = some _ _ _ from rfl,
      show vcFun C W (some _ _ h₂) = some _ _ _ from rfl,
      show vcFun C W (some _ _ _) = some _ _ _ from rfl, add_some hxyW]
    refine some_eq_some' ?_ ?_
    · rw [hslope, addX_variableChange]
    · rw [hslope, addY_variableChange]

variable (C W) in

private noncomputable def variableChangeAddEquiv : (C • W).toAffine.Point ≃+ W.Point :=
  { variableChangeEquiv C W with map_add' := vcFun_add }

@[scoped simp] private lemma variableChangeAddEquiv_apply (P : (C • W).toAffine.Point) :
    variableChangeAddEquiv C W P = vcFun C W P := rfl

@[scoped simp] private lemma variableChangeAddEquiv_symm_apply (P : W.Point) :
    (variableChangeAddEquiv C W).symm P = vcInvFun C W P := rfl

end Point
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point"

end Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine"

section SummingSetTransport

variable {K : Type*} [Field K] [DecidableEq K] (C : VariableChange K) (W : WeierstrassCurve K)

p2m_open "WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point"

omit [DecidableEq K] in

private lemma coordsOrZero_vcInvFun_of_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) :
    (vcInvFun C W.toAffine P).coordsOrZero = vcInvEmbedding C P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

private theorem variableChange_oddOrderSummingSet {Q : W.toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) :
    (C • W).oddOrderSummingSet ((variableChangeAddEquiv C W.toAffine).symm Q) n
      = (W.oddOrderSummingSet Q n).map (vcInvEmbedding C) := by
  unfold oddOrderSummingSet
  rw [Finset.map_eq_image, Finset.image_image]
  refine Finset.image_congr fun k hk => ?_
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk
  rw [← map_nsmul, variableChangeAddEquiv_symm_apply, Function.comp_apply]
  refine coordsOrZero_vcInvFun_of_ne_zero C W ?_
  intro h0
  have hdvd : 2 * n + 1 ∣ k := hQ ▸ addOrderOf_dvd_of_nsmul_eq_zero h0
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

end SummingSetTransport
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine"

section SplittingFieldVieta

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

private theorem Δ_eq_prod_two_torsion_roots {e₁ e₂ e₃ : K} (h2 : (2 : K) ≠ 0)
    (hroots : (Cubic.map (RingHom.id K) W.twoTorsionPolynomial).roots = {e₁, e₂, e₃}) :
    W.Δ = 16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2 := by
  have h4 : (4 : K) ≠ 0 := by
    intro h; apply h2
    have : (2 : K) * 2 = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h' <;> exact h'
  have ha : W.twoTorsionPolynomial.a = 4 := rfl
  have hdisc := Cubic.discr_eq_prod_three_roots (φ := RingHom.id K)
    (P := W.twoTorsionPolynomial) (ha ▸ h4) hroots
  simp only [RingHom.id_apply, ha] at hdisc
  rw [W.twoTorsionPolynomial_discr] at hdisc
  have h16 : (16 : K) ≠ 0 := by
    intro h; apply h2
    have : (2 : K) ^ 4 = 0 := by linear_combination h
    exact pow_eq_zero_iff (n := 4) (by omega) |>.mp this
  have : (16 : K) * W.Δ = 16 * (16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2) := by
    rw [hdisc]; ring
  exact mul_left_cancel₀ h16 this

private lemma four_ne_zero_of_two_ne_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    (4 : K) ≠ 0 := by
  intro h
  apply h2
  have : (2 : K) * 2 = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h' <;> exact h'

private theorem two_torsion_roots_sum [W.IsCharNeTwoNF] {e₁ e₂ e₃ : K} (h2 : (2 : K) ≠ 0)
    (hroots : (Cubic.map (RingHom.id K) W.twoTorsionPolynomial).roots = {e₁, e₂, e₃}) :
    e₁ + e₂ + e₃ = -W.a₂ := by
  have h4 : (4 : K) ≠ 0 := four_ne_zero_of_two_ne_zero h2
  have ha : W.twoTorsionPolynomial.a = 4 := rfl
  have hb : W.twoTorsionPolynomial.b = W.b₂ := rfl
  have := Cubic.b_eq_three_roots (φ := RingHom.id K) (ha ▸ h4) hroots
  simp only [RingHom.id_apply, ha, hb, W.b₂_of_isCharNeTwoNF] at this
  have key : W.a₂ = -(e₁ + e₂ + e₃) :=
    mul_left_cancel₀ h4 (by linear_combination this)
  linear_combination key

private theorem two_torsion_roots_esymm2 [W.IsCharNeTwoNF] {e₁ e₂ e₃ : K} (h2 : (2 : K) ≠ 0)
    (hroots : (Cubic.map (RingHom.id K) W.twoTorsionPolynomial).roots = {e₁, e₂, e₃}) :
    e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = W.a₄ := by
  have h4 : (4 : K) ≠ 0 := four_ne_zero_of_two_ne_zero h2
  have ha : W.twoTorsionPolynomial.a = 4 := rfl
  have hc : W.twoTorsionPolynomial.c = 2 * W.b₄ := rfl
  have := Cubic.c_eq_three_roots (φ := RingHom.id K) (ha ▸ h4) hroots
  simp only [RingHom.id_apply, ha, hc, W.b₄_of_isCharNeTwoNF] at this
  have key : W.a₄ = e₁ * e₂ + e₁ * e₃ + e₂ * e₃ :=
    mul_left_cancel₀ h4 (by linear_combination this)
  exact key.symm

private theorem two_torsion_roots_prod [W.IsCharNeTwoNF] {e₁ e₂ e₃ : K} (h2 : (2 : K) ≠ 0)
    (hroots : (Cubic.map (RingHom.id K) W.twoTorsionPolynomial).roots = {e₁, e₂, e₃}) :
    e₁ * e₂ * e₃ = -W.a₆ := by
  have h4 : (4 : K) ≠ 0 := four_ne_zero_of_two_ne_zero h2
  have ha : W.twoTorsionPolynomial.a = 4 := rfl
  have hd : W.twoTorsionPolynomial.d = W.b₆ := rfl
  have := Cubic.d_eq_three_roots (φ := RingHom.id K) (ha ▸ h4) hroots
  simp only [RingHom.id_apply, ha, hd, W.b₆_of_isCharNeTwoNF] at this
  have key : W.a₆ = -(e₁ * e₂ * e₃) :=
    mul_left_cancel₀ h4 (by linear_combination this)
  linear_combination key

end SplittingFieldVieta
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine"

section Descent

variable {R A : Type*} [CommRing R] [CommRing A] (W : WeierstrassCurve R) (f : R →+* A)

private lemma map_prod_veluU (S : Finset (R × R)) (hf : Function.Injective f) :
    ∏ P ∈ S.map ⟨Prod.map f f, hf.prodMap hf⟩, (W.map f).veluU P.1 P.2
      = f (∏ P ∈ S, W.veluU P.1 P.2) := by
  rw [Finset.prod_map, map_prod]
  exact Finset.prod_congr rfl fun P _ => by
    simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluU]

end Descent
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine"

section BModelWLOG

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

p2m_open "WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point"

private theorem identity_of_bModel [Invertible (2 : F)] {Q : W.toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1)
    (hcard : (W.oddOrderSummingSet Q n).card = n)
    (hbmodel : ((W.toCharNeTwoNF • W).veluQuotient
          ((W.toCharNeTwoNF • W).oddOrderSummingSet
            ((variableChangeAddEquiv W.toCharNeTwoNF W.toAffine).symm Q) n)).Δ *
        (∏ P ∈ (W.toCharNeTwoNF • W).oddOrderSummingSet
            ((variableChangeAddEquiv W.toCharNeTwoNF W.toAffine).symm Q) n,
          (W.toCharNeTwoNF • W).veluU P.1 P.2) ^ 4
      = (W.toCharNeTwoNF • W).Δ ^ (2 * n + 1)) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ *
        (∏ P ∈ W.oddOrderSummingSet Q n, W.veluU P.1 P.2) ^ 4
      = W.Δ ^ (2 * n + 1) := by
  rw [variableChange_oddOrderSummingSet W.toCharNeTwoNF W hQ] at hbmodel
  exact (identity_variableChange_iff W.toCharNeTwoNF W (W.oddOrderSummingSet Q n) n hcard).mp
    hbmodel

private theorem addOrderOf_variableChangeAddEquiv_symm (C : VariableChange F) {Q : W.toAffine.Point}
    {n : ℕ} (hQ : addOrderOf Q = 2 * n + 1) :
    addOrderOf ((variableChangeAddEquiv C W.toAffine).symm Q) = 2 * n + 1 := by
  rw [AddEquiv.addOrderOf_eq, hQ]

end BModelWLOG
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine"

namespace Affine
p2m_export "WeierstrassCurve.Affine" "map_slope Equation negY slope_of_X_ne map_a₃ slope map Point.some Point.X_eq_iff Nonsingular Point.add_self_of_Y_eq negAddY map_addY map_addX nonsingular_add slope_of_Y_ne Point addX map_a₁ Point.add_some nonsingular_neg Point.map equation_iff_nonsingular Point.some_ne_zero map_negY addY Y_eq_of_X_eq Point.add_of_X_ne equation_iff map_nonsingular polynomial Point.neg_some Point.add_self_of_Y_ne Point.coordsOrZero Point.coordsOrZero_zero Point.coordsOrZero_some vcX vcY vcXInv vcYInv vcXInv_vcX vcYInv_vcY"
namespace Point
p2m_export "WeierstrassCurve.Affine.Point" "add_of_Y_eq map_id map_map some some.injEq neg_zero X_eq_iff add_self_of_Y_eq map_zero add_some map some_ne_zero add_of_X_ne zero neg_some add_self_of_Y_ne mk coordsOrZero coordsOrZero_zero coordsOrZero_some vcFun vcInvFun variableChangeEquiv"
p2m_open "WeierstrassCurve.Affine.Point WeierstrassCurve.Affine"

section MapHom

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  (f : F →+* K) {W : WeierstrassCurve.Affine F}

private def mapFun : W.Point → (W.map f).toAffine.Point
  | 0 => 0
  | .some x y h => .some (f x) (f y) ((W.map_nonsingular f.injective x y).mpr h)

omit [DecidableEq F] [DecidableEq K] in
@[scoped simp] private lemma mapFun_zero : mapFun f (0 : W.Point) = 0 := rfl

omit [DecidableEq F] [DecidableEq K] in
@[scoped simp] private lemma mapFun_some {x y : F} (h : W.Nonsingular x y) :
    mapFun f (.some x y h) = .some (f x) (f y) ((W.map_nonsingular f.injective x y).mpr h) :=
  rfl

private lemma mapFun_add (P Q : W.Point) :
    mapFun f (P + Q) = mapFun f P + mapFun f Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
  · rw [add_of_Y_eq hxy.1 hxy.2, mapFun_zero, mapFun_some, mapFun_some,
      add_of_Y_eq (congr_arg f hxy.1) (by rw [hxy.2, map_negY])]
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂)) := fun h =>
      hxy ⟨f.injective h.1, f.injective (by rw [map_negY] at h; exact h.2)⟩
    rw [add_some hxy, mapFun_some, mapFun_some, mapFun_some, add_some hxy']
    refine some_eq_some' ?_ ?_ <;>
    · rw [map_slope]
      simp only [map_addX, map_addY]

private noncomputable def pointMapHom : W.Point →+ (W.map f).toAffine.Point where
  toFun := mapFun f
  map_zero' := rfl
  map_add' := mapFun_add f

@[scoped simp] private lemma pointMapHom_apply (P : W.Point) : pointMapHom f P = mapFun f P := rfl

omit [DecidableEq F] [DecidableEq K] in
private lemma mapFun_injective : Function.Injective (mapFun f (W := W)) := by
  rintro (_ | ⟨x₁, y₁, _⟩) (_ | ⟨x₂, y₂, _⟩) h
  · rfl
  · exact absurd h.symm (some_ne_zero _)
  · exact absurd h (some_ne_zero _)
  · simp only [mapFun_some, some.injEq] at h
    exact some_eq_some' (f.injective h.1) (f.injective h.2)

private lemma pointMapHom_injective : Function.Injective (pointMapHom f (W := W)) :=
  mapFun_injective f

end MapHom
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine"

end Affine.Point
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine"

section MapSummingSet

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  (f : F →+* K) (W : WeierstrassCurve F)

p2m_open "WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point"

omit [DecidableEq F] [DecidableEq K] in

private lemma coordsOrZero_mapFun_of_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) :
    (mapFun f P).coordsOrZero = (Prod.map f f) P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

private theorem map_oddOrderSummingSet {Q : W.toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) :
    (W.map f).oddOrderSummingSet (pointMapHom f Q) n
      = (W.oddOrderSummingSet Q n).map ⟨Prod.map f f, f.injective.prodMap f.injective⟩ := by
  unfold oddOrderSummingSet
  rw [Finset.map_eq_image, Finset.image_image]
  refine Finset.image_congr fun k hk => ?_
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk
  rw [← map_nsmul, pointMapHom_apply, Function.comp_apply, Function.Embedding.coeFn_mk]
  refine coordsOrZero_mapFun_of_ne_zero f W ?_
  intro h0
  have hdvd : 2 * n + 1 ∣ k := hQ ▸ addOrderOf_dvd_of_nsmul_eq_zero h0
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

omit [DecidableEq F] [DecidableEq K] in

private theorem identity_map_iff (S : Finset (F × F)) (n : ℕ) :
    ((W.map f).veluQuotient (S.map ⟨Prod.map f f, f.injective.prodMap f.injective⟩)).Δ *
        (∏ P ∈ S.map ⟨Prod.map f f, f.injective.prodMap f.injective⟩,
          (W.map f).veluU P.1 P.2) ^ 4
      = (W.map f).Δ ^ (2 * n + 1) ↔
    (W.veluQuotient S).Δ * (∏ P ∈ S, W.veluU P.1 P.2) ^ 4 = W.Δ ^ (2 * n + 1) := by
  rw [map_veluQuotient _ _ S f.injective, map_Δ, map_prod_veluU _ _ S f.injective, map_Δ,
    ← map_pow, ← map_pow, ← map_mul]
  exact f.injective.eq_iff

end MapSummingSet
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

namespace N5IDC2Aux4

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

variable {F : Type*} [Field F]

private noncomputable def ordNF (W : WeierstrassCurve F) (ha1 : W.a₁ ≠ 0) : VariableChange F :=
  ⟨Units.mk0 W.a₁ ha1, W.a₃ / W.a₁, 0, (W.a₄ + (W.a₃ / W.a₁) ^ 2) / W.a₁⟩

private lemma ordNF_u (W : WeierstrassCurve F) (ha1 : W.a₁ ≠ 0) :
    ((ordNF W ha1).u : F) = W.a₁ := rfl

private lemma ordNF_r (W : WeierstrassCurve F) (ha1 : W.a₁ ≠ 0) :
    (ordNF W ha1).r = W.a₃ / W.a₁ := rfl

private lemma ordNF_s (W : WeierstrassCurve F) (ha1 : W.a₁ ≠ 0) :
    (ordNF W ha1).s = 0 := rfl

private lemma ordNF_t (W : WeierstrassCurve F) (ha1 : W.a₁ ≠ 0) :
    (ordNF W ha1).t = (W.a₄ + (W.a₃ / W.a₁) ^ 2) / W.a₁ := rfl

private lemma ordNF_u_inv (W : WeierstrassCurve F) (ha1 : W.a₁ ≠ 0) :
    (((ordNF W ha1).u⁻¹ : Fˣ) : F) = W.a₁⁻¹ := by
  rw [Units.val_inv_eq_inv_val, ordNF_u]

private lemma ordNF_a₁ (W : WeierstrassCurve F) (ha1 : W.a₁ ≠ 0) :
    (ordNF W ha1 • W).a₁ = 1 := by
  rw [variableChange_a₁, ordNF_u_inv, ordNF_s, mul_zero, add_zero, inv_mul_cancel₀ ha1]

private lemma ordNF_a₃ (W : WeierstrassCurve F) (ha1 : W.a₁ ≠ 0) (h2 : (2 : F) = 0) :
    (ordNF W ha1 • W).a₃ = 0 := by
  rw [variableChange_a₃, ordNF_r, ordNF_t]
  have h : W.a₃ + W.a₃ / W.a₁ * W.a₁ + 2 * ((W.a₄ + (W.a₃ / W.a₁) ^ 2) / W.a₁) = 0 := by
    rw [div_mul_cancel₀ _ ha1]
    linear_combination (W.a₃ + (W.a₄ + (W.a₃ / W.a₁) ^ 2) / W.a₁) * h2
  rw [h, mul_zero]

private lemma ordNF_a₄ (W : WeierstrassCurve F) (ha1 : W.a₁ ≠ 0) (h2 : (2 : F) = 0) :
    (ordNF W ha1 • W).a₄ = 0 := by
  rw [variableChange_a₄, ordNF_r, ordNF_s, ordNF_t]
  have h : W.a₄ - 0 * W.a₃ + 2 * (W.a₃ / W.a₁) * W.a₂
      - ((W.a₄ + (W.a₃ / W.a₁) ^ 2) / W.a₁ + W.a₃ / W.a₁ * 0) * W.a₁ + 3 * (W.a₃ / W.a₁) ^ 2
      - 2 * 0 * ((W.a₄ + (W.a₃ / W.a₁) ^ 2) / W.a₁) = 0 := by
    have ht : (W.a₄ + (W.a₃ / W.a₁) ^ 2) / W.a₁ * W.a₁ = W.a₄ + (W.a₃ / W.a₁) ^ 2 :=
      div_mul_cancel₀ _ ha1
    linear_combination (W.a₃ / W.a₁ * W.a₂ + (W.a₃ / W.a₁) ^ 2) * h2 - ht
  rw [h, mul_zero]

end N5IDC2Aux4
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine toCharNeTwoNF isUnit_Δ b₄_of_isCharNeTwoNF Affine.negY a₁_of_isCharNeTwoNF Affine.slope_of_X_ne a₃ map_map a₁ twoTorsionPolynomial_discr map b₂ twoTorsionPolynomial variableChange_a₃ isElliptic_iff mk Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Δ_of_char_two Affine.Point.X_eq_iff variableChange_a₆ Affine.Point.add_self_of_Y_eq toCharNeTwoNF_spec IsCharNeTwoNF variableChange_Δ b₆_of_isCharNeTwoNF variableChange_a₂ Affine.nonsingular_add map_id a₃_of_isCharNeTwoNF toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Ψ₂Sq_eq Affine.Point.map b₆ b₈ variableChange_a₁ map_a₁ Affine.equation_iff_nonsingular b₂_of_isCharNeTwoNF Affine.Point.some_ne_zero variableChange_a₄ Δ VariableChange Affine.Point.add_of_X_ne Affine.equation_iff Affine.Point.neg_some Affine.Point.add_self_of_Y_ne j b₄ Δ' map_a₃ veluGx veluGy veluT veluU veluW veluT_eq veluU_eq_Ψ₂Sq_eval veluTSum veluWSum veluQuotient veluQuotient_a₁ veluQuotient_a₂ veluQuotient_a₃ veluQuotient_a₄ veluQuotient_a₆ veluQuotient_b₂ veluQuotient_b₄ veluQuotient_b₆ Affine.Point.coordsOrZero Affine.Point.coordsOrZero_zero Affine.Point.coordsOrZero_some oddOrderSummingSet mem_oddOrderSummingSet IsOddVeluSet veluX vcInvEmbedding vcInvEmbedding_apply variableChange_veluU variableChange_veluTSum variableChange_veluWSum map_veluU map_veluQuotient"
p2m_open "WeierstrassCurve"

section Seams

universe u

variable {F : Type u} [Field F] [DecidableEq F]

private theorem seam_identity_of_bModel [Invertible (2 : F)] (W : WeierstrassCurve F)
    [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ} (hQ : addOrderOf Q = 2 * n + 1)
    (hcard : (W.oddOrderSummingSet Q n).card = n)
    (hbmodel : ∀ (V : WeierstrassCurve F) (_ : V.a₁ = 0) (_ : V.a₃ = 0)
        [V.IsElliptic] (Q' : V.toAffine.Point) (_ : addOrderOf Q' = 2 * n + 1),
      (V.veluQuotient (V.oddOrderSummingSet Q' n)).Δ *
          (∏ P ∈ V.oddOrderSummingSet Q' n, V.veluU P.1 P.2) ^ 4
        = V.Δ ^ (2 * n + 1)) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ *
        (∏ P ∈ W.oddOrderSummingSet Q n, W.veluU P.1 P.2) ^ 4
      = W.Δ ^ (2 * n + 1) := by
  have hspec := W.toCharNeTwoNF_spec
  have ha₁' : (W.toCharNeTwoNF • W).a₁ = 0 := (W.toCharNeTwoNF • W).a₁_of_isCharNeTwoNF
  have ha₃' : (W.toCharNeTwoNF • W).a₃ = 0 := (W.toCharNeTwoNF • W).a₃_of_isCharNeTwoNF
  haveI : (W.toCharNeTwoNF • W).IsElliptic := by
    rw [isElliptic_iff, variableChange_Δ]
    exact (isUnit_of_invertible ((W.toCharNeTwoNF.u⁻¹ : Fˣ) : F)).pow 12 |>.mul W.isUnit_Δ
  have hQ' : addOrderOf
      ((Affine.Point.variableChangeAddEquiv W.toCharNeTwoNF W.toAffine).symm Q) = 2 * n + 1 :=
    addOrderOf_variableChangeAddEquiv_symm W W.toCharNeTwoNF hQ
  exact identity_of_bModel W hQ hcard (hbmodel _ ha₁' ha₃' _ hQ')

private theorem seam_identity_of_splits (W : WeierstrassCurve F) (ha₁ : W.a₁ = 0)
    (ha₃ : W.a₃ = 0) [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {Q : W.toAffine.Point} {n : ℕ} (hQ : addOrderOf Q = 2 * n + 1)
    (hcore : ∀ (K : Type u) [Field K] [DecidableEq K] [IsAlgClosed K] (_ : (2 : K) ≠ 0)
        (V : WeierstrassCurve K) (_ : V.a₁ = 0) (_ : V.a₃ = 0) [V.IsElliptic]
        (e₁ e₂ e₃ : K)
        (_ : (Cubic.map (RingHom.id K) V.twoTorsionPolynomial).roots = {e₁, e₂, e₃})
        (Q' : V.toAffine.Point) (_ : addOrderOf Q' = 2 * n + 1),
      (V.veluQuotient (V.oddOrderSummingSet Q' n)).Δ *
          (∏ P ∈ V.oddOrderSummingSet Q' n, V.veluU P.1 P.2) ^ 4
        = V.Δ ^ (2 * n + 1)) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ *
        (∏ P ∈ W.oddOrderSummingSet Q n, W.veluU P.1 P.2) ^ 4
      = W.Δ ^ (2 * n + 1) := by
  classical
  have _ := ha₁; have _ := ha₃
  let K := AlgebraicClosure F
  let ι : F →+* K := algebraMap F K
  have hι : Function.Injective ι := (algebraMap F K).injective
  have h2K : (2 : K) ≠ 0 := by
    have h2eq : ι (2 : F) = (2 : K) := map_ofNat ι 2
    rw [← h2eq]
    exact fun h => h2 (hι (h.trans (ι.map_zero).symm))
  let V := W.map ι
  have ha₁' : V.a₁ = 0 := by rw [show V.a₁ = ι W.a₁ from map_a₁ W ι, ha₁, ι.map_zero]
  have ha₃' : V.a₃ = 0 := by rw [show V.a₃ = ι W.a₃ from map_a₃ W ι, ha₃, ι.map_zero]
  have h4 : (4 : K) ≠ 0 := four_ne_zero_of_two_ne_zero h2K
  have ha : V.twoTorsionPolynomial.a ≠ 0 := h4
  have hsplits : (V.twoTorsionPolynomial.toPoly.map (RingHom.id K)).Splits :=
    IsAlgClosed.splits _
  obtain ⟨e₁, e₂, e₃, hroots⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplits
  let Q'' := Affine.Point.pointMapHom ι Q
  have hQ'' : addOrderOf Q'' = 2 * n + 1 := by
    rw [addOrderOf_injective (Affine.Point.pointMapHom ι) (Affine.Point.pointMapHom_injective ι) Q,
      hQ]
  have hK := hcore K h2K V ha₁' ha₃' e₁ e₂ e₃ hroots Q'' hQ''
  rw [map_oddOrderSummingSet ι W hQ] at hK
  exact (identity_map_iff ι W (W.oddOrderSummingSet Q n) n).mp hK

private theorem seam_core {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    (h2K : (2 : K) ≠ 0)
    (V : WeierstrassCurve K) (ha₁ : V.a₁ = 0) (ha₃ : V.a₃ = 0) [V.IsElliptic]
    (e₁ e₂ e₃ : K)
    (hroots : (Cubic.map (RingHom.id K) V.twoTorsionPolynomial).roots = {e₁, e₂, e₃})
    {n : ℕ} (Q' : V.toAffine.Point) (hQ' : addOrderOf Q' = 2 * n + 1) :
    (V.veluQuotient (V.oddOrderSummingSet Q' n)).Δ *
        (∏ P ∈ V.oddOrderSummingSet Q' n, V.veluU P.1 P.2) ^ 4
      = V.Δ ^ (2 * n + 1) :=
  haveI : V.IsCharNeTwoNF := ⟨ha₁, ha₃⟩
  have hσ1 := two_torsion_roots_sum V h2K hroots
  have hσ2 := two_torsion_roots_esymm2 V h2K hroots
  have hσ3 := two_torsion_roots_prod V h2K hroots
  N5IDAux1.core_assembly h2K V ha₁ ha₃ e₁ e₂ e₃ hroots Q' hQ'
    (fun W' _ _ _ h => Δ_eq_prod_two_torsion_roots W' h2K h)
    hσ1 hσ2 hσ3
    (fun g => N5IDAux4.sum_oddOrderSummingSet_eq hQ' g)
    (fun g => N5IDAux4.prod_oddOrderSummingSet_eq hQ' g)
    (N5IDAux4.multiset_map_double hQ')
    (fun _ haff hx m => N5IDAux4.xvSum_orbit_const' hQ' haff hx m)
    (fun _ _ _ hq h1 h2 h3 hd =>
      ⟨N5IDAux4.pack_esymm1 ha₁ ha₃ hσ1 hσ2 hσ3 hq h1 h2 h3 hd,
       N5IDAux4.pack_esymm2 ha₁ ha₃ hσ1 hσ2 hσ3 hq h1 h2 h3 hd,
       N5IDAux4.pack_esymm3 ha₁ ha₃ hσ1 hσ2 hσ3 hq h1 h2 h3 hd,
       N5IDAux4.pack_esymm4 ha₁ ha₃ hσ1 hσ2 hσ3 hq h1 h2 h3 hd⟩)
    (fun _ _ h hy => N5IDAux4.double_x_mul_psi2Sq ha₁ ha₃ h hy)
    (fun _ _ _ _ _ h1 h2 h3 hT hne =>
      N5IDAux4.addX_two_torsion_sub_root ha₁ ha₃ h1 h2 h3 hT hne)
    (N5IDAux1.good_abscissae_infinite ha₁ ha₃ h2K hQ')

private theorem char_two_ordinary_of_core (W : WeierstrassCurve F) [W.IsElliptic]
    (h2 : (2 : F) = 0) (ha1 : W.a₁ ≠ 0)
    {n : ℕ} {Q : W.toAffine.Point} (hQ : addOrderOf Q = 2 * n + 1)
    (hcard : (W.oddOrderSummingSet Q n).card = n)
    (hcore : ∀ (K : Type u) [Field K] [DecidableEq K] [IsAlgClosed K] (_ : (2 : K) = 0)
        (V : WeierstrassCurve K) (_ : V.a₁ = 1) (_ : V.a₃ = 0) (_ : V.a₄ = 0) [V.IsElliptic]
        (Q' : V.toAffine.Point) (_ : addOrderOf Q' = 2 * n + 1)
        (_ : (V.oddOrderSummingSet Q' n).card = n),
      (V.veluQuotient (V.oddOrderSummingSet Q' n)).Δ *
          (∏ P ∈ V.oddOrderSummingSet Q' n, V.veluU P.1 P.2) ^ 4
        = V.Δ ^ (2 * n + 1)) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ *
        (∏ P ∈ W.oddOrderSummingSet Q n, W.veluU P.1 P.2) ^ 4
      = W.Δ ^ (2 * n + 1) := by
  classical
  let K := AlgebraicClosure F
  let ι : F →+* K := algebraMap F K
  have hι : Function.Injective ι := (algebraMap F K).injective
  have h2K : (2 : K) = 0 := by
    have h2eq : ι (2 : F) = (2 : K) := map_ofNat ι 2
    rw [← h2eq, h2, ι.map_zero]
  let V := W.map ι
  have ha1K : V.a₁ ≠ 0 := by
    rw [show V.a₁ = ι W.a₁ from map_a₁ W ι]
    intro hc
    exact ha1 (hι (by rw [hc, ι.map_zero]))
  let Q2 := Affine.Point.pointMapHom ι Q
  have hQ2 : addOrderOf Q2 = 2 * n + 1 := by
    rw [addOrderOf_injective (Affine.Point.pointMapHom ι) (Affine.Point.pointMapHom_injective ι) Q,
      hQ]
  have hSmap : V.oddOrderSummingSet Q2 n
      = (W.oddOrderSummingSet Q n).map ⟨Prod.map ι ι, hι.prodMap hι⟩ :=
    map_oddOrderSummingSet ι W hQ
  have hcardK : (V.oddOrderSummingSet Q2 n).card = n := by
    rw [hSmap, Finset.card_map]
    exact hcard
  have hQ3 : addOrderOf
      ((Affine.Point.variableChangeAddEquiv (N5IDC2Aux4.ordNF V ha1K) V.toAffine).symm Q2)
      = 2 * n + 1 :=
    addOrderOf_variableChangeAddEquiv_symm V (N5IDC2Aux4.ordNF V ha1K) hQ2
  have hcardC : (((N5IDC2Aux4.ordNF V ha1K) • V).oddOrderSummingSet
      ((Affine.Point.variableChangeAddEquiv (N5IDC2Aux4.ordNF V ha1K) V.toAffine).symm Q2)
        n).card = n := by
    rw [variableChange_oddOrderSummingSet (N5IDC2Aux4.ordNF V ha1K) V hQ2, Finset.card_map]
    exact hcardK
  have hid_CV := hcore K h2K ((N5IDC2Aux4.ordNF V ha1K) • V)
    (N5IDC2Aux4.ordNF_a₁ V ha1K) (N5IDC2Aux4.ordNF_a₃ V ha1K h2K)
    (N5IDC2Aux4.ordNF_a₄ V ha1K h2K) _ hQ3 hcardC
  rw [variableChange_oddOrderSummingSet (N5IDC2Aux4.ordNF V ha1K) V hQ2] at hid_CV
  have hidV := (identity_variableChange_iff (N5IDC2Aux4.ordNF V ha1K) V
    (V.oddOrderSummingSet Q2 n) n hcardK).mp hid_CV
  rw [hSmap] at hidV
  exact (identity_map_iff ι W (W.oddOrderSummingSet Q n) n).mp hidV

private theorem seam_char_two_core {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    (h2K : (2 : K) = 0) (V : WeierstrassCurve K) (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0)
    (ha₄ : V.a₄ = 0) [V.IsElliptic] {n : ℕ} (Q' : V.toAffine.Point)
    (hQ' : addOrderOf Q' = 2 * n + 1) :
    (V.veluQuotient (V.oddOrderSummingSet Q' n)).Δ *
        (∏ P ∈ V.oddOrderSummingSet Q' n, V.veluU P.1 P.2) ^ 4
      = V.Δ ^ (2 * n + 1) :=
  N5IDAux1.char_two_ordinary_core_of h2K V ha₁ ha₃ ha₄ Q'
    (N5IDChar2.Δ_V h2K V ha₁ ha₃ ha₄)
    (N5IDChar2.row_iff_chain h2K V ha₁ ha₃ ha₄ hQ')
    (N5IDAux4.xvSum V Q' n)
    (N5IDChar2.xvSum_V h2K V ha₁ ha₃ ha₄ hQ')
    (fun _ hk => N5IDChar2.xk_ne_zero h2K V ha₁ ha₃ hQ'
      (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
    (N5IDAux4.xco_nsmul_injOn hQ')
    (fun _ hT0 hT2 j _ hk1 hkn => N5IDAux4.coset_xco_ne_kernel hQ' hT0 hT2 j hk1 hkn)
    (fun _ hT0 hT2 m => N5IDAux4.xvSum_coset hQ' hT0 hT2 m)

end Seams
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.WeierstrassCurve"

theorem solution
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ *
        (∏ P ∈ W.oddOrderSummingSet Q n, W.veluU P.1 P.2) ^ 4
      = W.Δ ^ (2 * n + 1) := by
  by_cases h2 : (2 : F) = 0
  ·

    by_cases ha1 : W.a₁ = 0
    · exact N5IDAux1.char_two_a₁_zero W h2 ha1 Q (N5IDAux4.card_oddOrderSummingSet' hQ)
    · exact char_two_ordinary_of_core W h2 ha1 hQ (N5IDAux4.card_oddOrderSummingSet' hQ)
        fun K _ _ _ h2K V ha₁ ha₃ ha₄ _ Q' hQ' _ => seam_char_two_core h2K V ha₁ ha₃ ha₄ Q' hQ'
  · haveI : Invertible (2 : F) := invertibleOfNonzero h2
    have hcard := N5IDAux4.card_oddOrderSummingSet' hQ
    refine seam_identity_of_bModel W hQ hcard fun V ha₁ ha₃ _ Q' hQ' => ?_
    exact seam_identity_of_splits V ha₁ ha₃ h2 hQ'
      fun K _ _ _ h2K V' ha₁' ha₃' _ e₁ e₂ e₃ hroots Q'' hQ'' =>
        seam_core h2K V' ha₁' ha₃' e₁ e₂ e₃ hroots Q'' hQ''

end S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
end P2MW
export P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow (solution)
