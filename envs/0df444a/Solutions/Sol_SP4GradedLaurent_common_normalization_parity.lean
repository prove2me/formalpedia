-- Prove2me | solution 1 for SP4GradedLaurent.common_normalization_parity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T01:58:24.749128+00:00
-- url     : https://prove2.me/submissions/ff2c2256-ab82-4780-8ef1-4645e8d5de58

import Definitions.Def_SP4GradedLaurent
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace SP4GradedLaurent

private theorem sign_add (a b : ℤ) : sign (a + b) = sign a * sign b := by
  simp [sign, Int.negOnePow_add]

private theorem sign_two_mul (a : ℤ) : sign (2 * a) = 1 := by
  simp [sign, Int.negOnePow_two_mul]

private theorem sign_neg_one : sign (-1) = -1 := by
  norm_num [sign, Int.negOnePow_neg]

private theorem euler_shift (k : ℤ) (P : GradedPolynomial) :
    euler (shift k P) = sign k * euler P := by
  change (P.mapDomain (fun m => k + m)).sum (fun m c => sign m * c) =
    sign k * P.sum (fun m c => sign m * c)
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]
  simp only [sign_add, mul_assoc, Finsupp.sum, Finset.mul_sum]

private theorem signedMoment_shift (k : ℤ) (P : GradedPolynomial) :
    signedMoment (shift k P) = sign k * (signedMoment P + k * euler P) := by
  change (P.mapDomain (fun m => k + m)).sum (fun m c => m * sign m * c) =
    sign k * (P.sum (fun m c => m * sign m * c) + k * P.sum (fun m c => sign m * c))
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]
  simp only [Finsupp.sum, sign_add]
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

private theorem euler_tensorV (P : GradedPolynomial) : euler (tensorV P) = 0 := by
  simp [tensorV, euler_shift, sign_neg_one]

private theorem signedMoment_tensorV (P : GradedPolynomial) :
    signedMoment (tensorV P) = euler P := by
  simp [tensorV, signedMoment_shift, sign_neg_one]

private theorem signedMoment_even_shift (k : ℤ) (P : GradedPolynomial)
    (hP : euler P = 0) : signedMoment (shift (2 * k) P) = signedMoment P := by
  simp [signedMoment_shift, sign_two_mul, hP]

private theorem euler_even_shift (k : ℤ) (P : GradedPolynomial) :
    euler (shift (2 * k) P) = euler P := by
  simp [euler_shift, sign_two_mul]

private theorem even_mass_sub_euler (P : GradedPolynomial) : Even (mass P - euler P) := by
  change Even ((P.sum fun _ c => 1 * c) - P.sum fun m c => sign m * c)
  simp only [Finsupp.sum, one_mul, ← Finset.sum_sub_distrib]
  apply Finset.even_sum
  intro m hm
  rcases Int.units_eq_one_or m.negOnePow with h | h
  · simp [sign, h]
  · simp only [sign, h, Units.val_neg, Units.val_one, neg_mul, one_mul, sub_neg_eq_add]
    exact ⟨P m, rfl⟩

/-- The top degree of a translated adjacent two-degree profile fixes its shift. -/
private theorem normalized_shift_unique (a b : ℤ)
    (h : tensorV (Finsupp.single a 1) = tensorV (Finsupp.single b 1)) : a = b := by
  have h' : Finsupp.single a (1 : ℤ) + Finsupp.single (a - 1) 1 =
      Finsupp.single b 1 + Finsupp.single (b - 1) 1 := by
    simpa only [tensorV, shift, Finsupp.mapDomain_single, show -1 + a = a - 1 by omega,
      show -1 + b = b - 1 by omega] using h
  by_contra hab
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have atb := congrArg (fun P : GradedPolynomial => P b) h'
    have h1 : a ≠ b := by omega
    have h2 : a - 1 ≠ b := by omega
    have h3 : b - 1 ≠ b := by omega
    simp [h1, h2, h3] at atb
  · have ata := congrArg (fun P : GradedPolynomial => P a) h'
    have h1 : b ≠ a := by omega
    have h2 : b - 1 ≠ a := by omega
    have h3 : a - 1 ≠ a := by omega
    simp [h1, h2, h3] at ata

end SP4GradedLaurent

open SP4GradedLaurent

/-- The Laurent-polynomial normalization obstruction. The row and column
identities are explicit polynomial hypotheses, not conclusions about an
unformalized Floer-theoretic construction. -/
theorem solution
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (flip : κ ≃ κ) (k : ι → κ → ℤ) (l : ι → ℤ)
    (X0 : κ → GradedPolynomial) (Xp Xm : ι → κ → GradedPolynomial)
    (U0 : GradedPolynomial) (Up Um Qp Qm : ι → GradedPolynomial)
    (G : κ → GradedPolynomial) (lam mu : ℤ)
    (hcell : ∀ i j, euler (Xp i j) = 0)
    (hconj : ∀ i j, Xm i (flip j) = shift (2 * k i j) (Xp i j))
    (htarget : ∀ i, Um i = shift (2 * l i) (Up i))
    (hrow0 : ∑ j, X0 j = tensorV (shift lam U0))
    (hrowp : ∀ i, ∑ j, Xp i j = tensorV (shift lam (Up i)) + tensorV (Qp i))
    (hrowm : ∀ i, ∑ j, Xm i j = tensorV (shift lam (Um i)) + tensorV (Qm i))
    (hcolumn : ∀ j, X0 j + ∑ i, Xp i j + ∑ i, Xm i j = tensorV (shift mu (G j)))
    (hU : euler U0 + ∑ i, euler (Up i) + ∑ i, euler (Um i) = 1)
    (hG : ∑ j, euler (G j) = 1)
    (hnorm : tensorV (Finsupp.single lam 1) = tensorV (Finsupp.single mu 1)) :
    lam = mu ∧ Even (∑ i, mass (Qp i)) := by
  classical
  have hshift : lam = mu := normalized_shift_unique lam mu hnorm
  have hmom (i : ι) : (∑ j, signedMoment (Xm i j)) = ∑ j, signedMoment (Xp i j) := by
    calc
      (∑ j, signedMoment (Xm i j)) = ∑ j, signedMoment (Xm i (flip j)) :=
        (flip.sum_comp (fun j => signedMoment (Xm i j))).symm
      _ = ∑ j, signedMoment (Xp i j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hconj, signedMoment_even_shift _ _ (hcell i j)]
  have hup (i : ι) : euler (Um i) = euler (Up i) := by
    rw [htarget, euler_even_shift]
  have hrp (i : ι) : (∑ j, signedMoment (Xp i j)) =
      sign lam * euler (Up i) + euler (Qp i) := by
    have h := congrArg signedMoment (hrowp i)
    simpa only [map_sum, map_add, signedMoment_tensorV, euler_shift] using h
  have hrm (i : ι) : (∑ j, signedMoment (Xm i j)) =
      sign lam * euler (Um i) + euler (Qm i) := by
    have h := congrArg signedMoment (hrowm i)
    simpa only [map_sum, map_add, signedMoment_tensorV, euler_shift] using h
  have hQ (i : ι) : euler (Qm i) = euler (Qp i) := by
    have h := hmom i
    rw [hrp, hrm, hup] at h
    linarith
  have hc := congrArg (fun F : κ → GradedPolynomial => ∑ j, signedMoment (F j))
    (funext hcolumn)
  simp only [map_add, map_sum, signedMoment_tensorV, euler_shift] at hc
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_comm (f := fun j i => signedMoment (Xp i j)),
    Finset.sum_comm (f := fun j i => signedMoment (Xm i j)),
    ← Finset.mul_sum, hG, mul_one] at hc
  have hr0 : (∑ j, signedMoment (X0 j)) = sign lam * euler U0 := by
    have h := congrArg signedMoment hrow0
    simpa only [map_sum, signedMoment_tensorV, euler_shift] using h
  simp_rw [hr0, hrp, hrm] at hc
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hc
  have hqsum : (∑ i, euler (Qm i)) = ∑ i, euler (Qp i) :=
    Finset.sum_congr rfl (fun i hi => hQ i)
  have htotal : sign lam * (euler U0 + ∑ i, euler (Up i) + ∑ i, euler (Um i)) +
      (∑ i, euler (Qp i)) + ∑ i, euler (Qm i) = sign mu := by
    linear_combination hc
  rw [hU, mul_one, hqsum, ← hshift] at htotal
  have hzero : (∑ i, euler (Qp i)) = 0 := by omega
  have heven : Even (∑ i, (mass (Qp i) - euler (Qp i))) :=
    Finset.even_sum _ (fun i hi => even_mass_sub_euler (Qp i))
  rw [Finset.sum_sub_distrib, hzero, sub_zero] at heven
  exact ⟨hshift, heven⟩
