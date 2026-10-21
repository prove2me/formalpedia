-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P11.universal_integer_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:11:53.688575+00:00
-- url     : https://prove2.me/submissions/f28ab775-b1cc-4e97-b28a-41080236e7a5

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
theorem solution (r : ℕ) (hr : 1 ≤ r) :
    (∀ (a : ℕ) (sigma : Equiv.Perm (Fin r)),
      MvPolynomial.rename sigma (universalH r a) = universalH r a) ∧
    (∀ (R : Type*) [CommRing R] (omega : ℕ → R) (u : Fin r → R),
      BMWAdmissible omega u → ∀ a : ℕ, omega a = evalH u a) := by
  refine ⟨fun a sigma => ?_, fun R _ omega u h => g66h_part2 r hr R omega u h⟩
  have := g66h_part1 r (MvPolynomial.rename sigma).toRingHom (fun j => by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.rename_X]
    exact g66h_signed_perm (fun i => (MvPolynomial.X i : MvPolynomial (Fin r) ℤ)) sigma j) a
  exact this
