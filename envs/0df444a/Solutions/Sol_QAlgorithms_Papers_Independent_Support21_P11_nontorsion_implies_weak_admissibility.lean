-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P11.nontorsion_implies_weak_admissibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:20:49.620664+00:00
-- url     : https://prove2.me/submissions/a506f629-9328-4086-99db-3a8cb8f401c6

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11
noncomputable section

open scoped BigOperators Classical

theorem g66h_x2pow {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (x1 x2 e : A)
    (h2 : x2 * e = -(x1 * e)) (h3 : x1 * x2 = x2 * x1) (m : ℕ) :
    x2 * (x1 ^ m * e) = -(x1 ^ (m+1) * e) := by
  have hc : Commute x2 (x1 ^ m) := (Commute.pow_right (h3.symm) m)
  rw [← mul_assoc, hc.eq, mul_assoc, h2, mul_neg, ← mul_assoc, pow_succ]

theorem g66h_skein {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (omega : ℕ → S)
    (x1 x2 s e : A)
    (h1 : s * x1 = x2 * s + e - 1) (h2 : x2 * e = -(x1 * e)) (h3 : x1 * x2 = x2 * x1)
    (h4 : s * e = e) (h5 : ∀ a, e * x1 ^ a * e = omega a • e) :
    ∀ a : ℕ, s * x1 ^ a * e = (-1 : S) ^ a • (x1 ^ a * e) +
      (∑ k ∈ Finset.range a, ((-1 : S) ^ k * omega (a - 1 - k)) • (x1 ^ k * e)) -
      (if Odd a then x1 ^ (a - 1) * e else 0) := by
  intro a
  induction a with
  | zero => simp [h4]
  | succ a ih =>
    have step : s * x1 ^ (a+1) * e = x2 * (s * x1 ^ a * e) + omega a • e - x1 ^ a * e := by
      rw [pow_succ', ← mul_assoc s, h1, ← h5 a]; noncomm_ring
    rw [step, ih, mul_sub, mul_add, mul_smul_comm, g66h_x2pow (S := S) x1 x2 e h2 h3, Finset.mul_sum]
    simp only [mul_smul_comm, g66h_x2pow (S := S) x1 x2 e h2 h3]
    rw [Finset.sum_range_succ' _ a]
    have hs : ∀ k ∈ Finset.range a, ((-1 : S) ^ (k+1) * omega (a + 1 - 1 - (k+1))) • (x1 ^ (k+1) * e)
        = ((-1 : S) ^ k * omega (a - 1 - k)) • -(x1 ^ (k + 1) * e) := by
      intro k hk
      rw [show a + 1 - 1 - (k+1) = a - 1 - k by omega, pow_succ, smul_neg, mul_comm _ (-1 : S),
        mul_assoc, neg_one_mul, neg_smul]
    rw [Finset.sum_congr rfl hs]
    simp only [Nat.add_sub_cancel, pow_zero, one_mul, Nat.sub_zero, Nat.odd_add_one]
    rcases Nat.even_or_odd a with he | ho
    · have hno : ¬ Odd a := Nat.not_odd_iff_even.mpr he
      simp only [hno, if_false, not_false_eq_true, if_true, mul_zero, sub_zero, pow_succ, mul_neg,
        mul_one, neg_smul, smul_neg]
      abel
    · have hno : ¬ ¬ Odd a := not_not.mpr ho
      have ha1 : a - 1 + 1 = a := by obtain ⟨m, rfl⟩ := ho; omega
      simp only [ho, hno, if_true, if_false, not_true_eq_false]
      rw [g66h_x2pow (S := S) x1 x2 e h2 h3 (a-1), ha1]
      simp only [pow_succ, mul_neg, mul_one, neg_smul, smul_neg]
      abel

theorem g66h_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a : ℕ) :
    ∑ b ∈ Finset.Icc 1 a, f b = ∑ k ∈ Finset.range a, f (k + 1) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

open QAlgorithms.Papers.Independent.Renew46.P16 in
theorem g66h_aff_rels (S : Type*) [CommRing S] (omega : ℕ → S) (n : ℕ) (hn : 2 ≤ n) :
    affineS S omega n 0 * affineX S omega n 0 =
        affineX S omega n 1 * affineS S omega n 0 + affineE S omega n 0 - 1 ∧
    affineX S omega n 1 * affineE S omega n 0 = -(affineX S omega n 0 * affineE S omega n 0) ∧
    affineX S omega n 0 * affineX S omega n 1 = affineX S omega n 1 * affineX S omega n 0 ∧
    affineS S omega n 0 * affineE S omega n 0 = affineE S omega n 0 ∧
    affineE S omega n 0 * affineS S omega n 0 = affineE S omega n 0 ∧
    (∀ a, affineE S omega n 0 * affineX S omega n 0 ^ a * affineE S omega n 0 =
      omega a • affineE S omega n 0) := by
  have q : ∀ {x y}, BMWRel S omega n x y → affineBMWQuotientMap S omega n x =
      affineBMWQuotientMap S omega n y := fun h => RingQuot.mkAlgHom_rel S h
  have r1 := q (BMWRel.skeinLeft 0 (by omega))
  have r2 := q (BMWRel.antisymRight 0 (by omega))
  have r3 := q (BMWRel.xxCommute 0 1 (by omega) (by omega))
  have r4 := q (BMWRel.se 0 (by omega))
  have r5 := q (BMWRel.es 0 (by omega))
  have r6 := q (BMWRel.idempotent 0 (by omega))
  have r7 : ∀ a, 0 < a → _ := fun a ha => q (BMWRel.unwrap a ha hn)
  simp only [map_sub, map_mul, map_one, map_add, map_zero, map_pow, AlgHom.commutes] at r1 r2 r3 r4 r5 r6 r7
  refine ⟨?_, ?_, r3, r4, r5, ?_⟩
  · change affineS S omega n 0 * affineX S omega n 0 - affineX S omega n 1 * affineS S omega n 0 =
      affineE S omega n 0 - 1 at r1
    rw [add_sub_assoc, ← r1]; abel
  · change (affineX S omega n 0 + affineX S omega n 1) * affineE S omega n 0 = 0 at r2
    rw [add_mul] at r2
    exact eq_neg_of_add_eq_zero_right r2
  · intro a
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [pow_zero, mul_one, ← pow_two, Algebra.smul_def]; exact r6
    · rw [Algebra.smul_def]; exact r7 a ha

open QAlgorithms.Papers.Independent.Renew46.P16 in
theorem g66h_aff_skein (S : Type*) [CommRing S] (omega : ℕ → S)
    (n a : ℕ) (hn : 2 ≤ n) :
    affineS S omega n 0 * affineX S omega n 0 ^ a * affineE S omega n 0 =
      (-1 : S) ^ a • (affineX S omega n 0 ^ a * affineE S omega n 0) +
      (∑ b ∈ Finset.Icc 1 a, ((-1 : S) ^ (b - 1) * omega (a - b)) •
        (affineX S omega n 0 ^ (b - 1) * affineE S omega n 0)) -
      (if Odd a then affineX S omega n 0 ^ (a - 1) * affineE S omega n 0 else 0) := by
  obtain ⟨h1, h2, h3, h4, -, h5⟩ := g66h_aff_rels S omega n hn
  rw [g66h_Icc, g66h_skein omega _ _ _ _ h1 h2 h3 h4 h5 a]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Nat.add_sub_cancel]
  congr 3
  omega

theorem g66h_odd_scalar {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (omega : ℕ → S)
    (x1 s e : A)
    (hskein : ∀ a : ℕ, s * x1 ^ a * e = (-1 : S) ^ a • (x1 ^ a * e) +
      (∑ k ∈ Finset.range a, ((-1 : S) ^ k * omega (a - 1 - k)) • (x1 ^ k * e)) -
      (if Odd a then x1 ^ (a - 1) * e else 0))
    (h5 : ∀ a, e * x1 ^ a * e = omega a • e) (h6 : e * s = e) (a : ℕ) (ha : Odd a) :
    (2 * omega a - (∑ b ∈ Finset.Icc 1 a, (-1 : S) ^ (b - 1) * omega (b - 1) * omega (a - b))
      + omega (a - 1)) • e = 0 := by
  have key := congrArg (e * ·) (hskein a)
  simp only [mul_add, mul_sub, mul_smul_comm, Finset.mul_sum, ha, if_true] at key
  simp only [← mul_assoc, h6, h5, smul_smul, ha.neg_one_pow] at key
  have hI : ∑ b ∈ Finset.Icc 1 a, (-1 : S) ^ (b - 1) * omega (b - 1) * omega (a - b) =
      ∑ k ∈ Finset.range a, (-1 : S) ^ k * omega (a - 1 - k) * omega k := by
    have : ∀ (f : ℕ → S) a, ∑ b ∈ Finset.Icc 1 a, f b = ∑ k ∈ Finset.range a, f (k + 1) := by
      intro f a
      induction a with
      | zero => simp
      | succ a ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
    rw [this]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Nat.add_sub_cancel, show a - (k+1) = a - 1 - k by omega]
    ring
  rw [hI]
  have hsum : (∑ k ∈ Finset.range a, (-1 : S) ^ k * omega (a - 1 - k) * omega k) • e =
      ∑ k ∈ Finset.range a, ((-1 : S) ^ k * omega (a - 1 - k) * omega k) • e := Finset.sum_smul ..
  rw [add_smul, sub_smul, hsum]
  linear_combination (norm := module) key

theorem g66h_rec {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (omega : ℕ → S)
    {r : ℕ} (u : Fin r → S) (x e : A)
    (h5 : ∀ a, e * x ^ a * e = omega a • e)
    (hP : (List.ofFn fun j : Fin r => x - algebraMap S A (u j)).prod = 0) (a : ℕ) :
    (∑ j ∈ Finset.range (r + 1),
      (∏ i : Fin r, (Polynomial.X - Polynomial.C (u i))).coeff j * omega (j + a)) • e = 0 := by
  set p : Polynomial S := ∏ i : Fin r, (Polynomial.X - Polynomial.C (u i)) with hp
  have h0 : Polynomial.aeval x p = 0 := by
    rw [hp, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
    simpa [Function.comp_def] using hP
  have hdeg : p.natDegree < r + 1 := by
    have : p.natDegree ≤ r := by
      rw [hp]
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      have h1 : ∑ i : Fin r, (Polynomial.X - Polynomial.C (u i)).natDegree ≤ ∑ _i : Fin r, (1 : ℕ) :=
        Finset.sum_le_sum (fun i _ => Polynomial.natDegree_X_sub_C_le (u i))
      have h2 : ∑ _i : Fin r, (1 : ℕ) = r := by simp
      omega
    omega
  rw [Polynomial.aeval_eq_sum_range' hdeg] at h0
  have := congrArg (fun z => e * x ^ a * z * e) h0
  simp only [mul_zero, zero_mul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc] at this
  rw [← this, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc e (x ^ a) (x ^ j), ← pow_add, h5, smul_smul, add_comm a j]

open QAlgorithms.Papers.Independent.Renew46.P16 in
theorem g66h_cyc_rels (S : Type*) [CommRing S] (omega : ℕ → S) (n r : ℕ) (u : Fin r → S)
    (hn : 2 ≤ n) :
    let x1 := cyclotomicX S omega n r u 0
    let x2 := cyclotomicX S omega n r u 1
    let s := cyclotomicS S omega n r u 0
    let e := cyclotomicE S omega n r u 0
    s * x1 = x2 * s + e - 1 ∧ x2 * e = -(x1 * e) ∧ x1 * x2 = x2 * x1 ∧ s * e = e ∧ e * s = e ∧
    (∀ a, e * x1 ^ a * e = omega a • e) ∧
    (List.ofFn fun j : Fin r => x1 - algebraMap S _ (u j)).prod = 0 := by
  intro x1 x2 s e
  obtain ⟨h1, h2, h3, h4, h6, h5⟩ := g66h_aff_rels S omega n hn
  set φ := cyclotomicMap S omega n r u
  have hP : φ (cyclotomicPolynomial S omega n r u) = 0 := by
    have := RingQuot.mkAlgHom_rel S
      (show cyclotomicRel S omega n r u (cyclotomicPolynomial S omega n r u) 0 from ⟨rfl, rfl⟩)
    rw [map_zero] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg φ h1; simp only [map_mul, map_add, map_sub, map_one] at this; exact this
  · have := congrArg φ h2; simp only [map_mul, map_neg] at this; exact this
  · have := congrArg φ h3; simp only [map_mul] at this; exact this
  · have := congrArg φ h4; simp only [map_mul] at this; exact this
  · have := congrArg φ h6; simp only [map_mul] at this; exact this
  · intro a; have := congrArg φ (h5 a); simp only [map_mul, map_pow, map_smul] at this; exact this
  · unfold cyclotomicPolynomial at hP
    rw [map_list_prod, List.map_ofFn] at hP
    simpa [Function.comp_def, x1, cyclotomicX, φ] using hP

open QAlgorithms.Papers.Independent.Support21.P11 QAlgorithms.Papers.Independent.Renew46.P16 in
theorem g66h_weak (R : Type*) [CommRing R]
    (omega : ℕ → R) (n r : ℕ) (u : Fin r → R) (hn : 2 ≤ n)
    (he : ∀ c : R, c • cyclotomicE R omega n r u 0 = 0 → c = 0) :
    WeaklyAdmissible omega u := by
  obtain ⟨h1, h2, h3, h4, h6, h5, hP⟩ := g66h_cyc_rels R omega n r u hn
  have hsk := g66h_skein omega (cyclotomicX R omega n r u 0) (cyclotomicX R omega n r u 1)
    (cyclotomicS R omega n r u 0) (cyclotomicE R omega n r u 0) h1 h2 h3 h4 h5
  refine ⟨fun a _ ha => ?_, fun a => ?_⟩
  · have := he _ (g66h_odd_scalar omega (cyclotomicX R omega n r u 0) (cyclotomicS R omega n r u 0) (cyclotomicE R omega n r u 0) hsk h5 h6 a ha)
    linear_combination this
  · exact he _ (g66h_rec omega u (cyclotomicX R omega n r u 0) (cyclotomicE R omega n r u 0) h5 hP a)

open QAlgorithms.Papers.Independent.Support21.P11 QAlgorithms.Papers.Independent.Renew46.P16 in
theorem solution (R : Type*) [CommRing R]
    (omega : ℕ → R) (n r : ℕ) (u : Fin r → R) (hn : 2 ≤ n) (hr : 1 ≤ r)
    (he : ∀ c : R, c • cyclotomicE R omega n r u 0 = 0 → c = 0) :
    WeaklyAdmissible omega u := g66h_weak R omega n r u hn he
