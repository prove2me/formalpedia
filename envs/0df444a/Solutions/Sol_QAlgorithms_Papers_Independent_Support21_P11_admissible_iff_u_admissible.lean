-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P11.admissible_iff_u_admissible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:40:55.602394+00:00
-- url     : https://prove2.me/submissions/2532e0e1-9d68-43fb-93ff-37f6cc436e88

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11
noncomputable section

open scoped BigOperators Classical

open QAlgorithms.Papers.Independent.Support21.P11

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

open QAlgorithms.Papers.Independent.Renew46.P16 in
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

theorem solution (R : Type*) [CommRing R] (omega : ℕ → R)
    (r : ℕ) (u : Fin r → R) (hr : 1 ≤ r) (h2 : IsUnit (2 : R)) :
    BMWAdmissible omega u ↔ UAdmissible omega u := by
  have hE : ∀ a, evalH u a = schurEta u a :=
    fun a => (g66h_part2 r hr R (schurEta u) u ⟨g68r_tri u h2, g68r_cyc u⟩ a).symm
  constructor
  · intro h a
    rw [g66h_part2 r hr R omega u h a, hE]
  · intro h
    have : omega = schurEta u := funext h
    subst this
    exact ⟨g68r_tri u h2, g68r_cyc u⟩
