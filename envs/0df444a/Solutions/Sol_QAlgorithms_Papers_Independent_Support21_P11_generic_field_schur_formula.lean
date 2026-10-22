-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P11.generic_field_schur_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:43:45.019432+00:00
-- url     : https://prove2.me/submissions/1b625784-8b6b-4492-9f05-68440547eca6

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


open QAlgorithms.Papers.Independent.Support21.P11

theorem g66h_signed_top' {A : Type*} [CommRing A] {r : ℕ} (u : Fin r → A) :
    signedCoeff u r = 1 := by
  nontriviality A
  unfold signedCoeff parameterPolynomial
  have hm : (∏ i : Fin r, (Polynomial.X - Polynomial.C (u i))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (u i))
  have hd : (∏ i : Fin r, (Polynomial.X - Polynomial.C (u i))).natDegree = r := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (u i))]
    simp [Polynomial.natDegree_X]
  have := hm.coeff_natDegree
  rwa [hd] at this

theorem g66h_sum_swap {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A] (N : ℕ)
    (f : ℕ → ℕ → R) (V : ℕ → A) :
    ∑ a ∈ Finset.range N, ∑ k ∈ Finset.range a, f a k • V k =
      ∑ k ∈ Finset.range N, (∑ a ∈ Finset.range N, if k < a then f a k else 0) • V k := by
  have h1 : ∀ a ∈ Finset.range N, ∑ k ∈ Finset.range a, f a k • V k =
      ∑ k ∈ Finset.range N, (if k < a then f a k else 0) • V k := by
    intro a ha
    have ha := Finset.mem_range.mp ha
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun k => k < a)]
    have e1 : (Finset.range N).filter (fun k => k < a) = Finset.range a := by
      ext k; simp; omega
    rw [e1, Finset.sum_eq_zero (s := (Finset.range N).filter (fun k => ¬ k < a))
        (fun k hk => by rw [if_neg (Finset.mem_filter.mp hk).2, zero_smul]), add_zero]
    exact Finset.sum_congr rfl (fun k hk => by rw [if_pos (Finset.mem_range.mp hk)])
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_smul]

theorem g66h_odd_shift {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A] (r : ℕ)
    (c : ℕ → R) (V : ℕ → A) :
    ∑ a ∈ Finset.range (r+1), c a • (if Odd a then V (a - 1) else 0) =
      ∑ k ∈ Finset.range (r+1), (if Odd (k+1) ∧ k + 1 < r + 1 then c (k+1) else 0) • V k := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [Nat.not_odd_zero, if_false, smul_zero, add_zero, lt_self_iff_false, and_false,
    zero_smul, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k hk
  have hk := Finset.mem_range.mp hk
  by_cases ho : Odd (k+1)
  · simp [ho, show k + 1 < r + 1 by omega]
  · simp [ho]

theorem g66h_tri {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (omega : ℕ → R)
    {r : ℕ} (u : Fin r → R) (x s e : A)
    (hskein : ∀ a : ℕ, s * x ^ a * e = (-1 : R) ^ a • (x ^ a * e) +
      (∑ k ∈ Finset.range a, ((-1 : R) ^ k * omega (a - 1 - k)) • (x ^ k * e)) -
      (if Odd a then x ^ (a - 1) * e else 0))
    (hp0 : ∑ a ∈ Finset.range (r+1), signedCoeff u a • (x ^ a * e) = 0)
    (hp1 : ∑ a ∈ Finset.range (r+1), signedCoeff u a • (s * x ^ a * e) = 0)
    (hli : LinearIndependent R (fun k : Fin r => x ^ (k : ℕ) * e)) :
    TriangularRelations omega u := by
  set c := signedCoeff u with hcdef
  have hcr : c r = 1 := g66h_signed_top' u
  set V : ℕ → A := fun k => x ^ k * e with hV
  let D : ℕ → R := fun k => c k * (-1) ^ k +
    (∑ a ∈ Finset.range (r+1), if k < a then c a * ((-1) ^ k * omega (a - 1 - k)) else 0) -
    (if Odd (k+1) ∧ k + 1 < r + 1 then c (k+1) else 0)
  have hD : ∑ k ∈ Finset.range (r+1), D k • V k = 0 := by
    rw [← hp1]
    simp only [hskein, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.smul_sum, smul_smul]
    simp only [D, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have e2 := g66h_sum_swap (r+1) (fun a k => c a * ((-1) ^ k * omega (a - 1 - k))) V
    have e3 := g66h_odd_shift r c V
    simp only [hV] at e2 e3 ⊢
    rw [e2, ← e3]
  have hDr : D r = (-1) ^ r := by
    simp only [D, hcr, one_mul, lt_self_iff_false, and_false, if_false, sub_zero]
    rw [Finset.sum_eq_zero (fun a ha => by
      rw [if_neg (by have := Finset.mem_range.mp ha; omega)]), add_zero]
  -- combine
  have hcomb : ∑ k ∈ Finset.range r, (D k - D r * c k) • V k = 0 := by
    have : ∑ k ∈ Finset.range (r+1), (D k - D r * c k) • V k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← smul_smul, ← Finset.smul_sum, hD]
      rw [show (∑ k ∈ Finset.range (r+1), c k • V k) = 0 from hp0, smul_zero, sub_zero]
    rw [Finset.sum_range_succ, hcr, mul_one, sub_self, zero_smul, add_zero] at this
    exact this
  rw [Finset.sum_range] at hcomb
  have hz := (Fintype.linearIndependent_iff.mp hli) _ hcomb
  intro j hj
  have hj' := hz ⟨j, hj⟩
  simp only [hDr] at hj'
  simp only [D] at hj'
  -- reindex the inner sum
  have hre : (∑ a ∈ Finset.range (r+1), if j < a then c a * ((-1) ^ j * omega (a - 1 - j)) else 0)
      = (-1) ^ j * ∑ mu ∈ Finset.range (r - j), omega mu * c (mu + j + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_filter]
    have : (Finset.range (r+1)).filter (fun a => j < a) = Finset.Ico (j+1) (r+1) := by
      ext a; simp; omega
    rw [this, Finset.sum_Ico_eq_sum_range, show r + 1 - (j+1) = r - j by omega]
    apply Finset.sum_congr rfl
    intro mu _
    rw [show j + 1 + mu - 1 - j = mu by omega, show j + 1 + mu = mu + j + 1 by omega]
    ring
  rw [hre] at hj'
  simp only [show j + 1 < r + 1 by omega, and_true] at hj'
  have hsq : ((-1 : R) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; simp
  have hrj : ((-1 : R) ^ r) = (-1) ^ (r - j) * (-1) ^ j := by rw [← pow_add]; congr 1; omega
  unfold triangularRhs
  rw [← hcdef]
  rcases Nat.even_or_odd j with hje | hjo
  · have h1 : ¬ Odd (j + 1) = False := by simp [Nat.odd_add_one, hje]
    simp only [Nat.odd_add_one, Nat.not_odd_iff_even.mpr hje, not_true_eq_false, not_false_eq_true,
      if_true, hje, hje.neg_one_pow] at hj' ⊢
    rcases Nat.even_or_odd (r - j) with hre | hro
    · simp only [Nat.not_odd_iff_even.mpr hre, if_false, zero_add]
      rw [hrj, hre.neg_one_pow, hje.neg_one_pow] at hj'
      linear_combination hj'
    · simp only [hro, if_true]
      rw [hrj, hro.neg_one_pow, hje.neg_one_pow] at hj'
      linear_combination hj'
  · simp only [Nat.odd_add_one, hjo, not_true_eq_false, if_false, Nat.not_even_iff_odd.mpr hjo,
      hjo.neg_one_pow, add_zero, sub_zero] at hj' ⊢
    rcases Nat.even_or_odd (r - j) with hre | hro
    · simp only [Nat.not_odd_iff_even.mpr hre, if_false]
      rw [hrj, hre.neg_one_pow, hjo.neg_one_pow] at hj'
      linear_combination -hj'
    · simp only [hro, if_true]
      rw [hrj, hro.neg_one_pow, hjo.neg_one_pow] at hj'
      linear_combination -hj'

theorem g66h_psum {S A : Type*} [CommRing S] [Ring A] [Algebra S A]
    {r : ℕ} (u : Fin r → S) (x : A)
    (hP : (List.ofFn fun j : Fin r => x - algebraMap S A (u j)).prod = 0) :
    ∑ j ∈ Finset.range (r + 1),
      (∏ i : Fin r, (Polynomial.X - Polynomial.C (u i))).coeff j • x ^ j = 0 := by
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
  exact h0

theorem g66h_tors {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {r : ℕ} (hr : 0 < r)
    (x e : A) (hli : LinearIndependent R (fun k : Fin r => x ^ (k : ℕ) * e)) :
    ∀ c : R, c • e = 0 → c = 0 := by
  intro c hc
  have hli' := Fintype.linearIndependent_iff.mp hli
  set i0 : Fin r := ⟨0, hr⟩
  have hsum : ∑ j : Fin r, (if j = i0 then c else 0) • (x ^ (j : ℕ) * e) = 0 := by
    rw [Fintype.sum_eq_single i0 (fun j hj => by rw [if_neg hj, zero_smul]), if_pos rfl]
    simpa [i0] using hc
  have key := hli' _ hsum i0
  simpa using key

open QAlgorithms.Papers.Independent.Renew46.P16 in
theorem g66h_main (R : Type*) [CommRing R]
    (omega : ℕ → R) (n r : ℕ) (u : Fin r → R) (hn : 2 ≤ n) (hr : 1 ≤ r)
    (hli : LinearIndependent R
      (fun k : Fin r => cyclotomicX R omega n r u 0 ^ (k : ℕ) * cyclotomicE R omega n r u 0)) :
    WeaklyAdmissible omega u ∧ TriangularRelations omega u := by
  have he : ∀ c : R, c • cyclotomicE R omega n r u 0 = 0 → c = 0 :=
    g66h_tors (by omega) (cyclotomicX R omega n r u 0) (cyclotomicE R omega n r u 0) hli
  refine ⟨g66h_weak R omega n r u hn he, ?_⟩
  obtain ⟨h1, h2, h3, h4, h6, h5, hP⟩ := g66h_cyc_rels R omega n r u hn
  have hsk := g66h_skein omega (cyclotomicX R omega n r u 0) (cyclotomicX R omega n r u 1)
    (cyclotomicS R omega n r u 0) (cyclotomicE R omega n r u 0) h1 h2 h3 h4 h5
  have hs := g66h_psum u (cyclotomicX R omega n r u 0) hP
  have hp0 := congrArg (· * cyclotomicE R omega n r u 0) hs
  have hp1 := congrArg (fun z => cyclotomicS R omega n r u 0 * z * cyclotomicE R omega n r u 0) hs
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, zero_mul, mul_zero,
    ← mul_assoc] at hp0 hp1
  exact g66h_tri omega u (cyclotomicX R omega n r u 0) (cyclotomicS R omega n r u 0)
    (cyclotomicE R omega n r u 0) hsk hp0 hp1 hli


def g66h_F (r : ℕ) (n : ℕ) : ℕ → MvPolynomial (Fin r) ℤ :=
  (Nat.rec (motive := fun _ : ℕ => ℕ → MvPolynomial (Fin r) ℤ)
    (fun _ : ℕ => (0 : MvPolynomial (Fin r) ℤ))
    (fun k previous => Function.update previous k (universalHStep r previous k)) n)

theorem g66h_F_succ (r n : ℕ) :
    g66h_F r (n+1) = Function.update (g66h_F r n) n (universalHStep r (g66h_F r n) n) := rfl

theorem g66h_H_eq (r a : ℕ) : universalH r a = g66h_F r (a+1) a := rfl

theorem g66h_F_stable (r : ℕ) : ∀ n m, m < n → g66h_F r n m = universalH r m := by
  intro n
  induction n with
  | zero => intro m h; omega
  | succ n ih =>
    intro m hm
    rw [g66h_F_succ]
    rcases Nat.lt_or_ge m n with h | h
    · rw [Function.update_of_ne (by omega), ih m h]
    · have : m = n := by omega
      subst this
      rfl

theorem g66h_step_congr (r k : ℕ) (f g : ℕ → MvPolynomial (Fin r) ℤ)
    (h : ∀ m < k, f m = g m) : universalHStep r f k = universalHStep r g k := by
  unfold universalHStep
  simp only
  split_ifs with h1 h2
  · congr 1
    apply Finset.sum_congr rfl
    intro mu hmu
    rw [h mu (Finset.mem_range.mp hmu)]
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [h _ (by have := Finset.mem_range.mp hj; omega)]
  · rfl

theorem g66h_H_step (r k : ℕ) : universalH r k = universalHStep r (universalH r) k := by
  rw [g66h_H_eq, g66h_F_succ, Function.update_self]
  exact g66h_step_congr r k _ _ (fun m hm => g66h_F_stable r k m hm)

/-- coefficient images under a ring hom -/
theorem g66h_signed_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {r : ℕ}
    (u : Fin r → A) (j : ℕ) : φ (signedCoeff u j) = signedCoeff (fun i => φ (u i)) j := by
  unfold signedCoeff parameterPolynomial
  rw [← Polynomial.coeff_map, Polynomial.map_prod]
  simp

theorem g66h_rhs_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {r : ℕ}
    (u : Fin r → A) (j : ℕ) : φ (triangularRhs u j) = triangularRhs (fun i => φ (u i)) j := by
  unfold triangularRhs
  split_ifs <;> simp [g66h_signed_map, map_ofNat]

theorem g66h_signed_perm {A : Type*} [CommRing A] {r : ℕ} (u : Fin r → A) (σ : Equiv.Perm (Fin r))
    (j : ℕ) : signedCoeff (fun i => u (σ i)) j = signedCoeff u j := by
  unfold signedCoeff parameterPolynomial
  congr 1
  exact Fintype.prod_equiv σ _ _ (fun _ => rfl)

theorem g66h_signed_top {A : Type*} [CommRing A] {r : ℕ} (u : Fin r → A) :
    signedCoeff u r = 1 := by
  nontriviality A
  unfold signedCoeff parameterPolynomial
  have hm : (∏ i : Fin r, (Polynomial.X - Polynomial.C (u i))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (u i))
  have hd : (∏ i : Fin r, (Polynomial.X - Polynomial.C (u i))).natDegree = r := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (u i))]
    simp [Polynomial.natDegree_X]
  have := hm.coeff_natDegree
  rwa [hd] at this

theorem g66h_step_map' {B : Type*} [CommRing B] (r k : ℕ) (φ : MvPolynomial (Fin r) ℤ →+* B)
    (f : ℕ → MvPolynomial (Fin r) ℤ) (v : Fin r → B) (hv : (fun i => φ (MvPolynomial.X i)) = v) :
    φ (universalHStep r f k) =
      if k < r then
        triangularRhs v (r - 1 - k) -
          ∑ mu ∈ Finset.range k, φ (f mu) * signedCoeff v (mu + (r-1-k) + 1)
      else if 0 < r then
        - ∑ j ∈ Finset.range r, signedCoeff v j * φ (f (j + (k - r)))
      else 0 := by
  subst hv
  unfold universalHStep
  simp only
  split_ifs <;> simp [map_sum, g66h_signed_map, g66h_rhs_map]

theorem g66h_step_map {B : Type*} [CommRing B] (r k : ℕ) (φ : MvPolynomial (Fin r) ℤ →+* B)
    (f : ℕ → MvPolynomial (Fin r) ℤ) :
    φ (universalHStep r f k) =
      if k < r then
        triangularRhs (fun i => φ (MvPolynomial.X i)) (r - 1 - k) -
          ∑ mu ∈ Finset.range k, φ (f mu) * signedCoeff (fun i => φ (MvPolynomial.X i)) (mu + (r-1-k) + 1)
      else if 0 < r then
        - ∑ j ∈ Finset.range r, signedCoeff (fun i => φ (MvPolynomial.X i)) j * φ (f (j + (k - r)))
      else 0 := by
  unfold universalHStep
  simp only
  split_ifs <;> simp [map_sum, g66h_signed_map, g66h_rhs_map]

theorem g66h_part1 (r : ℕ) (φ : MvPolynomial (Fin r) ℤ →+* MvPolynomial (Fin r) ℤ)
    (hs : ∀ j, signedCoeff (fun i => φ (MvPolynomial.X i)) j =
        signedCoeff (fun i => MvPolynomial.X i) j) :
    ∀ a, φ (universalH r a) = universalH r a := by
  have ht : ∀ j, triangularRhs (fun i => φ (MvPolynomial.X i)) j =
      triangularRhs (fun i => MvPolynomial.X i) j := by
    intro j; unfold triangularRhs; simp only [hs]
  intro a
  induction a using Nat.strong_induction_on with
  | _ k ih =>
    have e1 := g66h_step_map r k φ (universalH r)
    have e2 := g66h_step_map r k (RingHom.id _) (universalH r)
    simp only [RingHom.id_apply] at e2
    rw [g66h_H_step, e1, e2]
    split_ifs with h1 h2
    · rw [ht]
      refine congrArg (_ - ·) (Finset.sum_congr rfl ?_)
      intro mu hmu
      rw [ih mu (Finset.mem_range.mp hmu), hs]
    · refine congrArg Neg.neg (Finset.sum_congr rfl ?_)
      intro j hj
      rw [ih _ (by have := Finset.mem_range.mp hj; omega), hs]
    · exact Eq.refl _

theorem g66h_part2 (r : ℕ) (hr : 1 ≤ r) (R : Type*) [CommRing R] (omega : ℕ → R) (u : Fin r → R)
    (h : BMWAdmissible omega u) : ∀ a : ℕ, omega a = evalH u a := by
  obtain ⟨htri, hrec⟩ := h
  intro a
  induction a using Nat.strong_induction_on with
  | _ k ih =>
    have e := g66h_step_map' r k (MvPolynomial.eval₂Hom (Int.castRingHom R) u) (universalH r) u
      (by funext i; simp)
    simp only [MvPolynomial.coe_eval₂Hom] at e
    have hev : evalH u k = MvPolynomial.eval₂ (Int.castRingHom R) u (universalH r k) := rfl
    rw [hev, g66h_H_step, e]
    split_ifs with h1 h2
    · have t := htri (r - 1 - k) (by omega)
      have hrk : r - (r - 1 - k) = k + 1 := by omega
      rw [hrk, Finset.sum_range_succ, show k + (r - 1 - k) + 1 = r by omega, g66h_signed_top,
        mul_one] at t
      rw [← t]
      have hsum : ∑ mu ∈ Finset.range k,
          MvPolynomial.eval₂ (Int.castRingHom R) u (universalH r mu) * signedCoeff u (mu + (r - 1 - k) + 1)
          = ∑ x ∈ Finset.range k, omega x * signedCoeff u (x + (r - 1 - k) + 1) := by
        apply Finset.sum_congr rfl
        intro mu hmu
        rw [ih mu (Finset.mem_range.mp hmu)]
        rfl
      rw [hsum]; ring
    · have t := hrec (k - r)
      rw [Finset.sum_range_succ, g66h_signed_top, one_mul, show r + (k - r) = k by omega] at t
      rw [eq_neg_iff_add_eq_zero, add_comm, ← t]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih _ (by have := Finset.mem_range.mp hj; omega)]
      rfl
    · omega

open QAlgorithms.Papers.Independent.Renew46.P16
theorem g68r_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a : ℕ) :
    ∑ b ∈ Finset.Icc 1 a, f b = ∑ k ∈ Finset.range a, f (k + 1) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

theorem g68r_coeff_lin {R : Type*} [CommRing R] (c : R) (F : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff (n+1) ((1 + PowerSeries.C c * PowerSeries.X) * F) =
      PowerSeries.coeff (n+1) F + c * PowerSeries.coeff n F := by
  rw [add_mul, one_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]

theorem g68r_coeff_lin0 {R : Type*} [CommRing R] (c : R) (F : PowerSeries R) :
    PowerSeries.coeff 0 ((1 + PowerSeries.C c * PowerSeries.X) * F) =
      PowerSeries.coeff 0 F := by
  rw [add_mul, one_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul]
  simp

theorem g68r_step {R : Type*} [CommRing R] (u : R) (l : List R) :
    (1 + PowerSeries.C (-u) * PowerSeries.X) * PowerSeries.mk (schurQList (u :: l)) =
      (1 + PowerSeries.C u * PowerSeries.X) * PowerSeries.mk (schurQList l) := by
  ext n
  cases n with
  | zero =>
    rw [g68r_coeff_lin0, g68r_coeff_lin0]
    simp [schurQList]
  | succ n =>
    rw [g68r_coeff_lin, g68r_coeff_lin]
    simp only [PowerSeries.coeff_mk, schurQList]
    rw [g68r_Icc, g68r_Icc, Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right]
    have : ∀ i ∈ Finset.range n, 2 * u ^ (i + 1 + 1) * schurQList l (n - (i + 1))
        = u * (2 * u ^ (i + 1) * schurQList l (n - (i + 1))) := by
      intro i hi; ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    simp only [zero_add, pow_one, Nat.sub_zero]
    ring

theorem g68r_list {R : Type*} [CommRing R] (l : List R) :
    (l.map (fun u => 1 + PowerSeries.C (-u) * PowerSeries.X)).prod * PowerSeries.mk (schurQList l) =
      (l.map (fun u => 1 + PowerSeries.C u * PowerSeries.X)).prod := by
  induction l with
  | nil => ext n; simp [schurQList, PowerSeries.coeff_one]
  | cons u l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← ih, mul_assoc, mul_comm, mul_assoc, mul_comm _ (1 + _), g68r_step]
    ring

theorem g68r_reflect1 {R : Type*} [CommRing R] (a : R) :
    Polynomial.reflect 1 (Polynomial.X - Polynomial.C a) = 1 + Polynomial.C (-a) * Polynomial.X := by
  ext i
  rcases i with _ | _ | i <;> simp [Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_C]

theorem g68r_reflect {R : Type*} [CommRing R] : ∀ (r : ℕ) (u : Fin r → R),
    Polynomial.reflect r (parameterPolynomial u) = ∏ i, (1 + Polynomial.C (-u i) * Polynomial.X) ∧
    (parameterPolynomial u).natDegree ≤ r := by
  intro r
  induction r with
  | zero => intro u; simp [parameterPolynomial]
  | succ r ih =>
    intro u
    obtain ⟨h1, h2⟩ := ih (fun i => u i.succ)
    have hp : parameterPolynomial u = (Polynomial.X - Polynomial.C (u 0)) * parameterPolynomial (fun i => u i.succ) := by
      simp [parameterPolynomial, Fin.prod_univ_succ]
    have hd1 : (Polynomial.X - Polynomial.C (u 0)).natDegree ≤ 1 := Polynomial.natDegree_X_sub_C_le _
    refine ⟨?_, ?_⟩
    · have := Polynomial.reflect_mul _ _ hd1 h2
      rw [add_comm 1 r] at this
      rw [hp, this, h1, g68r_reflect1, Fin.prod_univ_succ]
    · rw [hp]; exact (Polynomial.natDegree_mul_le).trans (by omega)

theorem g68r_E_coeff {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) (k : ℕ) :
    PowerSeries.coeff k (∏ i, (1 + PowerSeries.C (-u i) * PowerSeries.X)) =
      if k ≤ r then signedCoeff u (r - k) else 0 := by
  obtain ⟨h1, h2⟩ := g68r_reflect r u
  have : (∏ i, (1 + PowerSeries.C (-u i) * PowerSeries.X) : PowerSeries R) =
      ((Polynomial.reflect r (parameterPolynomial u) : Polynomial R) : PowerSeries R) := by
    rw [h1, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp
  rw [this, Polynomial.coeff_coe, Polynomial.coeff_reflect]
  simp only [signedCoeff]
  split_ifs with h
  · rw [Polynomial.revAt_le h]
  · rw [Polynomial.revAt_eq_self_of_lt (by omega)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem g68r_F_eq {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) :
    (∏ i, (1 + PowerSeries.C (u i) * PowerSeries.X) : PowerSeries R) =
      PowerSeries.rescale (-1 : R) (∏ i, (1 + PowerSeries.C (-u i) * PowerSeries.X)) := by
  rw [map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_add, map_one, map_mul, PowerSeries.rescale_X]
  have : PowerSeries.rescale (-1 : R) (PowerSeries.C (-u i)) = PowerSeries.C (-u i) := by
    ext n; simp [PowerSeries.coeff_C]; split_ifs <;> simp_all
  rw [this, ← mul_assoc, ← map_mul]
  simp

theorem g68r_main_ps {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) :
    (∏ i, (1 + PowerSeries.C (-u i) * PowerSeries.X)) * PowerSeries.mk (schurQ u) =
      (∏ i, (1 + PowerSeries.C (u i) * PowerSeries.X) : PowerSeries R) := by
  have := g68r_list (List.ofFn u)
  show _ * PowerSeries.mk (schurQList (List.ofFn u)) = _
  simpa [List.map_ofFn, List.prod_ofFn] using this

theorem g68r_q0 {R : Type*} [CommRing R] (l : List R) : schurQList l 0 = 1 := by
  induction l with
  | nil => simp [schurQList]
  | cons u l ih => simp [schurQList, ih]

theorem g68r_conv {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) (N : ℕ) :
    ∑ k ∈ Finset.range (N+1),
      PowerSeries.coeff k (∏ i, (1 + PowerSeries.C (-u i) * PowerSeries.X)) * schurQ u (N - k) =
    (-1) ^ N * PowerSeries.coeff N (∏ i, (1 + PowerSeries.C (-u i) * PowerSeries.X)) := by
  have h := congrArg (PowerSeries.coeff N) (g68r_main_ps u)
  rw [g68r_F_eq u, PowerSeries.coeff_rescale, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i _ * PowerSeries.coeff j _)] at h
  simpa using h

theorem g68r_ext {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) (g : ℕ → R) (N : ℕ) (hN : r ≤ N) :
    ∑ k ∈ Finset.range (r+1),
      PowerSeries.coeff k (∏ i, (1 + PowerSeries.C (-u i) * PowerSeries.X)) * g k =
    ∑ k ∈ Finset.range (N+1),
      PowerSeries.coeff k (∏ i, (1 + PowerSeries.C (-u i) * PowerSeries.X)) * g k := by
  apply Finset.sum_subset
  · intro k hk; simp at hk ⊢; omega
  · intro k hk hk'
    simp at hk hk'
    rw [g68r_E_coeff, if_neg (by omega), zero_mul]

theorem g68r_cyc {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) :
    CyclotomicRecurrence (schurEta u) u := by
  intro a
  set E : PowerSeries R := ∏ i, (1 + PowerSeries.C (-u i) * PowerSeries.X) with hE
  have he := g68r_E_coeff u
  rw [← Finset.sum_range_reflect]
  have h1 : ∀ k ∈ Finset.range (r+1), signedCoeff u (r + 1 - 1 - k) * schurEta u (r + 1 - 1 - k + a)
      = PowerSeries.coeff k E * schurQ u (r + a + 1 - k)
        - Ring.inverse (2:R) * (-1) ^ r * (PowerSeries.coeff k E * schurQ u (r + a - k))
        + PowerSeries.coeff k E * (if k = r + a then Ring.inverse (2:R) else 0) := by
    intro k hk
    simp at hk
    rw [he, if_pos (by omega)]
    have e1 : r + 1 - 1 - k + a = r + a - k := by omega
    have e2 : r + a - k + 1 = r + a + 1 - k := by omega
    rw [e1, schurEta, e2]
    have e3 : (r + a - k = 0) ↔ (k = r + a) := by omega
    simp only [Nat.add_sub_cancel, e3]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    g68r_ext u _ (r + a + 1) (by omega), g68r_ext u _ (r + a) (by omega), g68r_conv, g68r_conv,
    he, he, if_neg (by omega)]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Finset.sum_eq_single r]
    · simp only [add_zero, if_pos le_rfl, Nat.sub_self, if_true]
      rw [show PowerSeries.coeff r E = signedCoeff u 0 by rw [hE, he]; simp]
      have : ((-1:R)^r * (-1)^r) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
      linear_combination (- Ring.inverse (2:R) * signedCoeff u 0) * this
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  · rw [if_neg (by omega), Finset.sum_eq_zero]
    · simp
    · intro b hb; simp at hb; simp [show b ≠ r + a by omega]

theorem g68r_tri {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) (h2 : IsUnit (2 : R)) :
    TriangularRelations (schurEta u) u := by
  intro j hj
  obtain ⟨M, hM⟩ : ∃ M, r = M + j + 1 := ⟨r - j - 1, by omega⟩
  set E : PowerSeries R := ∏ i, (1 + PowerSeries.C (-u i) * PowerSeries.X) with hE
  have he := g68r_E_coeff u
  have hrj : r - j = M + 1 := by omega
  rw [hrj, ← Finset.sum_range_reflect]
  have h1 : ∀ k ∈ Finset.range (M+1), schurEta u (M + 1 - 1 - k) * signedCoeff u (M + 1 - 1 - k + j + 1)
      = PowerSeries.coeff k E * schurQ u (M + 1 - k)
        - Ring.inverse (2:R) * (-1) ^ r * (PowerSeries.coeff k E * schurQ u (M - k))
        + PowerSeries.coeff k E * (if k = M then Ring.inverse (2:R) else 0) := by
    intro k hk
    simp at hk
    rw [he, if_pos (by omega)]
    have e1 : M + 1 - 1 - k = M - k := by omega
    have e2 : M - k + 1 = M + 1 - k := by omega
    have e4 : r - k = M - k + j + 1 := by omega
    rw [e1, schurEta, e2, e4]
    have e3 : (M - k = 0) ↔ (k = M) := by omega
    simp only [e3]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    g68r_conv]
  have hs := g68r_conv u (M+1)
  rw [Finset.sum_range_succ, Nat.sub_self, show schurQ u 0 = 1 from g68r_q0 _, ← hE] at hs
  rw [← hE, eq_sub_of_add_eq hs, Finset.sum_eq_single M]
  rotate_left
  · intro b _ hb; rw [if_neg hb, mul_zero]
  · intro h; simp at h
  simp only [if_true]
  rw [show PowerSeries.coeff M E = signedCoeff u (j+1) by rw [hE, he, if_pos (by omega)]; congr 1; omega,
      show PowerSeries.coeff (M+1) E = signedCoeff u j by rw [hE, he, if_pos (by omega)]; congr 1; omega]
  have hinv : Ring.inverse (2:R) * 2 = 1 := Ring.inverse_mul_cancel _ h2
  unfold triangularRhs
  rw [hrj]
  subst hM
  rcases Nat.even_or_odd M with hMe | hMo <;> rcases Nat.even_or_odd j with hje | hjo
  · have o1 : Odd (M+1) := hMe.add_one
    have o2 : Odd (M + j + 1) := by rw [add_assoc, add_comm j 1, ← add_assoc]; exact (o1.add_even hje)
    rw [if_pos o1, if_pos hje, o1.neg_one_pow, o2.neg_one_pow, hMe.neg_one_pow]
    linear_combination (signedCoeff u (j+1)) * hinv
  · have o1 : Odd (M+1) := hMe.add_one
    have o2 : Even (M + j + 1) := by rw [add_assoc]; exact hMe.add (hjo.add_one)
    have : ¬ Even j := Nat.not_even_iff_odd.mpr hjo
    rw [if_pos o1, if_neg this, o1.neg_one_pow, o2.neg_one_pow, hMe.neg_one_pow]
    ring
  · have o1 : ¬ Odd (M+1) := Nat.not_odd_iff_even.mpr hMo.add_one
    have o1' : Even (M+1) := hMo.add_one
    have o2 : Even (M + j + 1) := by rw [add_assoc, add_comm j 1, ← add_assoc]; exact o1'.add hje
    rw [if_neg o1, if_pos hje, o1'.neg_one_pow, o2.neg_one_pow, hMo.neg_one_pow]
    linear_combination (signedCoeff u (j+1)) * hinv
  · have o1 : ¬ Odd (M+1) := Nat.not_odd_iff_even.mpr hMo.add_one
    have o1' : Even (M+1) := hMo.add_one
    have o2 : Odd (M + j + 1) := by rw [add_assoc]; exact hMo.add_even (hjo.add_one)
    have : ¬ Even j := Nat.not_even_iff_odd.mpr hjo
    rw [if_neg o1, if_neg this, o1'.neg_one_pow, o2.neg_one_pow, hMo.neg_one_pow]
    ring

theorem solution (F : Type*) [Field F] (omega : ℕ → F)
    (r : ℕ) (u : Fin r → F) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (hdistinct : Function.Injective u) (hsum : ∀ i j : Fin r, u i + u j ≠ 0)
    (hli : LinearIndependent F (idealFamily F omega r u))
    (hcorner : NonzeroCorner F omega r u) :
    ∀ a : ℕ, omega a = schurEta u a := by
  have h2' : IsUnit (2 : F) := isUnit_iff_ne_zero.mpr h2
  obtain ⟨hw, ht⟩ := g66h_main F omega 2 r u le_rfl hr hli
  intro a
  rw [g66h_part2 r hr F omega u ⟨ht, hw.2⟩ a,
    ← g66h_part2 r hr F (schurEta u) u ⟨g68r_tri u h2', g68r_cyc u⟩ a]
