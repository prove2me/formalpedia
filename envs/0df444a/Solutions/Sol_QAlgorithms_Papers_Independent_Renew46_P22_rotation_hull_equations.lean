-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P22.rotation_hull_equations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T04:20:19.984182+00:00
-- url     : https://prove2.me/submissions/d7fd1b2b-f6f4-4329-8c92-2c49f11d003d

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P22.X8RH

open MvPolynomial

variable {K : Type*} [Field K]

/-- dual-number Taylor expansion, first component -/
theorem taylor_fst {σ : Type*} [Fintype σ] (x v : σ → K) (p : MvPolynomial σ K) :
    (aeval (fun j => (TrivSqZeroExt.inl (x j) + TrivSqZeroExt.inr (v j) : DualNumber K)) p).fst
      = eval x p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq => simp only [map_add, TrivSqZeroExt.fst_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, TrivSqZeroExt.fst_mul, hp, aeval_X, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, eval_X]

theorem taylor_snd {σ : Type*} [Fintype σ] [DecidableEq σ] (x v : σ → K) (p : MvPolynomial σ K) :
    (aeval (fun j => (TrivSqZeroExt.inl (x j) + TrivSqZeroExt.inr (v j) : DualNumber K)) p).snd
      = ∑ j, v j * eval x (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
    simp only [map_add, TrivSqZeroExt.snd_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, TrivSqZeroExt.snd_mul, hp, taylor_fst]
    simp only [aeval_X, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      add_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
      smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X, mul_add,
      Finset.sum_add_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, map_one, map_zero]
    simp only [apply_ite (eval x), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun _ _ => by ring)


@[simp] theorem unc (M : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    Function.uncurry M (i, j) = M i j := rfl

/-- the rotation generator over `K` -/
def J : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

/-- entries of `x * J` as polynomials -/
def XJ (kl : Fin 2 × Fin 2) : Poly 2 K := ∑ m, X (kl.1, m) * C (J m kl.2)

/-- the left-invariant derivation attached to `J` -/
def Dd : Derivation K (Poly 2 K) (Poly 2 K) := ∑ kl, XJ (K := K) kl • pderiv kl

theorem eval_Dd (y : Fin 2 × Fin 2 → K) (q : Poly 2 K) :
    eval y (Dd q) = ∑ kl : Fin 2 × Fin 2, (∑ m, y (kl.1, m) * J m kl.2) * eval y (pderiv kl q) := by
  have : (Dd (K := K)) q = ∑ kl : Fin 2 × Fin 2, XJ kl * pderiv kl q := by
    rw [Dd, ← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    simp [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply]
  rw [this, map_sum]
  simp [XJ]

theorem mem_vI (H : Set (GeometricGL 2 K)) (p : Poly 2 K) :
    p ∈ vanishingIdeal K H ↔ ∀ a ∈ H, eval (Function.uncurry (a : Matrix (Fin 2) (Fin 2) K)) p = 0 := by
  simp [vanishingIdeal, MvPolynomial.mem_vanishingIdeal_iff]

theorem stab (H : Subgroup (GeometricGL 2 K))
    (hJ : ∀ p ∈ vanishingIdeal K (H : Set (GeometricGL 2 K)),
      ∑ ij : Fin 2 × Fin 2, J ij.1 ij.2 * eval (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) K))
        (pderiv ij p) = 0)
    (q : Poly 2 K) (hq : q ∈ vanishingIdeal K (H : Set (GeometricGL 2 K))) :
    Dd q ∈ vanishingIdeal K (H : Set (GeometricGL 2 K)) := by
  rw [mem_vI] at hq ⊢
  intro a ha
  set g : Fin 2 × Fin 2 → Poly 2 K := fun kl => ∑ m, C ((a : Matrix (Fin 2) (Fin 2) K) kl.1 m) * X (m, kl.2)
  have h1 : bind₁ g q ∈ vanishingIdeal K (H : Set (GeometricGL 2 K)) := by
    rw [mem_vI]
    intro b hb
    have e := aeval_bind₁ (R := K) (Function.uncurry (b : Matrix (Fin 2) (Fin 2) K)) g q
    rw [aeval_eq_eval] at e
    rw [e]
    have : (fun kl => eval (Function.uncurry (b : Matrix (Fin 2) (Fin 2) K)) (g kl)) =
        Function.uncurry ((a * b : GeometricGL 2 K) : Matrix (Fin 2) (Fin 2) K) := by
      funext kl
      obtain ⟨k, l⟩ := kl
      simp [g, Matrix.mul_apply, Units.val_mul, unc]
    rw [this, aeval_eq_eval]
    exact hq _ (H.mul_mem ha hb)
  have h2 := hJ _ h1
  have h3 := taylor_snd (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) K))
    (fun ij => J ij.1 ij.2) (bind₁ g q)
  rw [← h3, aeval_bind₁] at h2
  have : (fun kl => aeval (fun j => (TrivSqZeroExt.inl (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) K) j)
      + TrivSqZeroExt.inr (J j.1 j.2) : DualNumber K)) (g kl)) =
      fun kl => (TrivSqZeroExt.inl (Function.uncurry (a : Matrix (Fin 2) (Fin 2) K) kl)
        + TrivSqZeroExt.inr (∑ m, (a : Matrix (Fin 2) (Fin 2) K) kl.1 m * J m kl.2)) := by
    funext kl
    apply TrivSqZeroExt.ext
    · obtain ⟨k, l⟩ := kl
      fin_cases l <;> simp [g, Matrix.one_apply, TrivSqZeroExt.algebraMap_eq_inl,
        unc]
    · simp [g, TrivSqZeroExt.algebraMap_eq_inl]
  rw [this, taylor_snd] at h2
  rw [eval_Dd]; exact h2


theorem Dd_C (a : K) : Dd (K := K) (C a) = 0 := by
  rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _

theorem Dd_X (kl : Fin 2 × Fin 2) : Dd (K := K) (X kl) = XJ kl := by
  have : (Dd (K := K)) (X kl) = ∑ kl' : Fin 2 × Fin 2, XJ kl' * pderiv kl' (X kl) := by
    rw [Dd, ← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    simp [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply]
  rw [this]
  simp [pderiv_X, Pi.single_apply]

section Bpart

variable [CharZero K] (i : K)

/-- the substitution `(a,b) ↦ (z,w)` -/
def φv (kl : Fin 2 × Fin 2) : MvPolynomial (Fin 2) K :=
  (!![C (1/2) * (X 0 + X 1), C (-(i/2)) * (X 0 - X 1);
      C (i/2) * (X 0 - X 1), C (1/2) * (X 0 + X 1)] : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) K))
    kl.1 kl.2

/-- the Euler-type derivation `z ∂_z - w ∂_w` -/
def Ee : Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K) :=
  (X 0 : MvPolynomial (Fin 2) K) • pderiv 0 - (X 1 : MvPolynomial (Fin 2) K) • pderiv 1

theorem Ee_X0 : Ee (K := K) (X 0) = X 0 := by simp [Ee, pderiv_X]
theorem Ee_X1 : Ee (K := K) (X 1) = -X 1 := by simp [Ee, pderiv_X]
theorem Ee_C (a : K) : Ee (K := K) (C a) = 0 := by
  rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _

theorem Ee_base (hi : i * i = -1) (kl : Fin 2 × Fin 2) :
    Ee (φv i kl) = C (-i) * bind₁ (φv i) (XJ kl) := by
  obtain ⟨k, l⟩ := kl
  fin_cases k <;> fin_cases l <;>
  · simp only [φv, XJ, J, Fin.sum_univ_two, map_add, map_mul, map_sub, bind₁_X_right, bind₁_C_right,
      Derivation.leibniz, Ee_X0, Ee_X1, Ee_C, smul_zero, add_zero, smul_eq_mul]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_one, Matrix.head_cons,
      map_neg, map_one, map_zero]
    have hci : (C i : MvPolynomial (Fin 2) K) * C i = -1 := by rw [← map_mul, hi, map_neg, map_one]
    have h2 : (C (i / 2) : MvPolynomial (Fin 2) K) = C i * C (1 / 2) := by rw [← map_mul]; ring_nf
    have h3 : (C (-(i / 2)) : MvPolynomial (Fin 2) K) = -(C i * C (1 / 2)) := by
      rw [← map_mul, ← map_neg]; ring_nf
    simp only [h2, h3, Derivation.leibniz, map_add, map_sub, map_neg, Ee_X0, Ee_X1, Ee_C, smul_zero,
      add_zero, smul_eq_mul]
    first
    | ring1
    | linear_combination (C (1 / 2) * (X 0 - X 1)) * hci
    | linear_combination (-C (1 / 2) * (X 0 - X 1)) * hci
    | linear_combination (C (1 / 2) * (X 0 + X 1)) * hci
    | linear_combination (-C (1 / 2) * (X 0 + X 1)) * hci
    | linear_combination (C i * C (1 / 2) * (X 0 - X 1)) * hci
    | linear_combination (-C i * C (1 / 2) * (X 0 - X 1)) * hci
    | linear_combination (C i * C (1 / 2) * (X 0 + X 1)) * hci
    | linear_combination (-C i * C (1 / 2) * (X 0 + X 1)) * hci

theorem relE (hi : i * i = -1) (q : Poly 2 K) :
    Ee (bind₁ (φv i) q) = C (-i) * bind₁ (φv i) (Dd q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp only [bind₁_C_right, Ee_C, Dd_C, map_zero, mul_zero]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add]
  | mul_X p kl hp =>
    simp only [map_mul, bind₁_X_right, Derivation.leibniz, smul_eq_mul, hp, Ee_base i hi, Dd_X,
      map_add]
    ring

theorem relE_iter (hi : i * i = -1) (k : ℕ) (q : Poly 2 K) :
    (Ee (K := K))^[k] (bind₁ (φv i) q) = C ((-i) ^ k) * bind₁ (φv i) ((Dd (K := K))^[k] q) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Derivation.leibniz,
      Ee_C, smul_zero, add_zero, relE i hi, smul_eq_mul, pow_succ, map_mul]
    ring

theorem eval_one_bind (q : Poly 2 K) :
    eval (fun _ => (1 : K)) (bind₁ (φv i) q) = eval (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) K)) q := by
  have e := aeval_bind₁ (R := K) (fun _ : Fin 2 => (1 : K)) (φv i) q
  rw [aeval_eq_eval] at e
  rw [e, aeval_eq_eval]
  congr 2
  funext kl
  obtain ⟨k, l⟩ := kl
  fin_cases k <;> fin_cases l <;> simp [φv] <;> norm_num

theorem Ee_monomial (m : Fin 2 →₀ ℕ) (c : K) :
    Ee (K := K) (monomial m c) = monomial m (((m 0 : K) - m 1) * c) := by
  simp only [Ee, Derivation.coe_sub, Pi.sub_apply, Derivation.smul_apply, smul_eq_mul, pderiv_monomial]
  rw [X, X, monomial_mul, monomial_mul]
  by_cases h0 : m 0 = 0 <;> by_cases h1 : m 1 = 0
  · simp [h0, h1]
  · have e1 : Finsupp.single 1 1 + (m - Finsupp.single 1 1) = m := by
      ext t; fin_cases t <;> simp [h0] <;> omega
    simp [h0, e1, sub_mul, mul_comm]
  · have e0 : Finsupp.single 0 1 + (m - Finsupp.single 0 1) = m := by
      ext t; fin_cases t <;> simp [h1] <;> omega
    simp [h1, e0, sub_mul, mul_comm]
  · have e0 : Finsupp.single 0 1 + (m - Finsupp.single 0 1) = m := by
      ext t; fin_cases t <;> simp <;> omega
    have e1 : Finsupp.single 1 1 + (m - Finsupp.single 1 1) = m := by
      ext t; fin_cases t <;> simp <;> omega
    rw [e0, e1, ← map_sub (monomial m)]
    congr 1; ring

theorem Ee_iter_eval (k : ℕ) (P : MvPolynomial (Fin 2) K) :
    eval (fun _ => (1 : K)) ((Ee (K := K))^[k] P) =
      ∑ m ∈ P.support, ((m 0 : K) - m 1) ^ k * coeff m P := by
  have : (Ee (K := K))^[k] P = ∑ m ∈ P.support, monomial m (((m 0 : K) - m 1) ^ k * coeff m P) := by
    induction k with
    | zero => simpa using (P.as_sum)
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Ee_monomial, pow_succ]; congr 1; ring
  rw [this, map_sum]
  simp [eval_monomial]

omit [CharZero K] in
theorem polyQ {ι : Type*} (S : Finset ι) (c : ι → K) (x : ι → K)
    (h : ∀ k : ℕ, ∑ s ∈ S, x s ^ k * c s = 0) (Q : Polynomial K) :
    ∑ s ∈ S, Q.eval (x s) * c s = 0 := by
  simp_rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [h k, mul_zero]

theorem lagr {ι : Type*} (S : Finset ι) (c : ι → K) (n : ι → ℤ)
    (h : ∀ k : ℕ, ∑ s ∈ S, (n s : K) ^ k * c s = 0) (t : K) :
    ∑ s ∈ S, c s * t ^ (n s) = 0 := by
  classical
  have hz : ∀ z : ℤ, ∑ s ∈ S.filter (fun s => n s = z), c s = 0 := by
    intro z
    set Q : Polynomial K := ∏ w ∈ (S.image n).erase z, (Polynomial.X - Polynomial.C (w : K))
    have := polyQ S c (fun s => (n s : K)) h Q
    have hv : ∀ s ∈ S, Q.eval (n s : K) * c s = if n s = z then Q.eval (z : K) * c s else 0 := by
      intro s hs
      split_ifs with hs'
      · rw [hs']
      · rw [Polynomial.eval_prod, Finset.prod_eq_zero (i := n s)]
        · simp
        · exact Finset.mem_erase.2 ⟨hs', Finset.mem_image_of_mem n hs⟩
        · simp
    rw [Finset.sum_congr rfl hv, ← Finset.sum_filter, ← Finset.mul_sum] at this
    have hQz : Q.eval (z : K) ≠ 0 := by
      rw [Polynomial.eval_prod]
      refine Finset.prod_ne_zero_iff.2 (fun w hw => ?_)
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
      intro e
      exact (Finset.ne_of_mem_erase hw) (Int.cast_injective e).symm
    exact (mul_eq_zero.1 this).resolve_left hQz
  rw [← Finset.sum_fiberwise_of_maps_to (g := n) (t := S.image n)
    (fun s hs => Finset.mem_image_of_mem n hs)]
  apply Finset.sum_eq_zero
  intro z _
  rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.1 hs).2]), ← Finset.sum_mul, hz z,
    zero_mul]

theorem eval_laurent (P : MvPolynomial (Fin 2) K) (t : K) (ht : t ≠ 0) :
    eval ![t, t⁻¹] P = ∑ m ∈ P.support, coeff m P * t ^ ((m 0 : ℤ) - m 1) := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Fin.prod_univ_two, zpow_sub₀ ht]
  simp [div_eq_mul_inv, inv_pow]

theorem vanish_on_T (hi : i * i = -1) (p : Poly 2 K)
    (hD : ∀ k : ℕ, eval (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) K)) ((Dd (K := K))^[k] p) = 0)
    (a : Matrix (Fin 2) (Fin 2) K) (h1 : a 0 0 ^ 2 + a 0 1 ^ 2 = 1) (h2 : a 1 0 = -a 0 1)
    (h3 : a 1 1 = a 0 0) :
    eval (Function.uncurry a) p = 0 := by
  set P := bind₁ (φv i) p
  have hk : ∀ k : ℕ, ∑ m ∈ P.support, (((m 0 : ℤ) - m 1 : ℤ) : K) ^ k * coeff m P = 0 := by
    intro k
    have := Ee_iter_eval k P
    rw [relE_iter i hi, eval_mul, eval_C, eval_one_bind, hD k, mul_zero] at this
    push_cast; exact this.symm
  set t := a 0 0 + i * a 0 1
  have htt : t * (a 0 0 - i * a 0 1) = 1 := by
    linear_combination h1 - (a 0 1) ^ 2 * hi
  have ht : t ≠ 0 := left_ne_zero_of_mul_eq_one htt
  have hinv : t⁻¹ = a 0 0 - i * a 0 1 := (eq_inv_of_mul_eq_one_right htt).symm
  have hL := lagr P.support (fun m => coeff m P) (fun m => (m 0 : ℤ) - m 1) hk t
  rw [← eval_laurent P t ht] at hL
  have e := aeval_bind₁ (R := K) ![t, t⁻¹] (φv i) p
  rw [aeval_eq_eval] at e
  rw [e, aeval_eq_eval] at hL
  convert hL using 2
  congr 1
  funext kl
  obtain ⟨k, l⟩ := kl
  have h2' : (2 : K) ≠ 0 := two_ne_zero
  fin_cases k <;> fin_cases l <;> simp [φv, hinv, h2, h3, t] <;> field_simp <;>
  first
  | ring1
  | linear_combination (a 0 1) * hi
  | linear_combination (-(a 0 1)) * hi
  | linear_combination (2 * a 0 1) * hi
  | linear_combination (-(2 * a 0 1)) * hi
  | linear_combination (3 * a 0 1) * hi
  | linear_combination (-(3 * a 0 1)) * hi
  | linear_combination (4 * a 0 1) * hi
  | linear_combination (-(4 * a 0 1)) * hi

omit [CharZero K] in
theorem fiber_zero {ι : Type*} (S : Finset ι) (c : ι → K) (e : ι → ℕ)
    (h : ∀ d, ∑ s ∈ S.filter (fun s => e s = d), c s = 0) (f : ℕ → K) :
    ∑ s ∈ S, c s * f (e s) = 0 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := e) (t := S.image e)
    (fun s hs => Finset.mem_image_of_mem e hs)]
  apply Finset.sum_eq_zero
  intro z _
  rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.1 hs).2]), ← Finset.sum_mul, h z,
    zero_mul]

omit [CharZero K] in
theorem laur_zero [Infinite K] (P : MvPolynomial (Fin 2) K)
    (h : ∀ t : K, t ≠ 0 → eval ![t, t⁻¹] P = 0) :
    ∑ m ∈ P.support, ((m 0 : K) - m 1) * coeff m P = 0 := by
  classical
  set N : ℕ := ∑ m ∈ P.support, m 1
  have hN : ∀ m ∈ P.support, m 1 ≤ N := fun m hm =>
    Finset.single_le_sum (f := fun m : Fin 2 →₀ ℕ => m 1) (fun _ _ => Nat.zero_le _) hm
  set e : (Fin 2 →₀ ℕ) → ℕ := fun m => m 0 + N - m 1
  set Q : Polynomial K := ∑ m ∈ P.support, Polynomial.C (coeff m P) * Polynomial.X ^ (e m)
  have hQ : ∀ t : K, t ≠ 0 → Q.eval t = 0 := by
    intro t ht
    have h1 : Q.eval t = t ^ N * eval ![t, t⁻¹] P := by
      rw [MvPolynomial.eval_eq', Finset.mul_sum]
      simp only [Q, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Fin.prod_univ_two]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, inv_pow]
      have hm1 := hN m hm
      have : t ^ (e m) * (t ^ m 1) = t ^ N * t ^ m 0 := by
        rw [← pow_add, ← pow_add]; congr 1; simp only [e]; omega
      field_simp
      linear_combination (coeff m P) * this
    rw [h1, h t ht, mul_zero]
  have hQ0 : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := {t : K | t ≠ 0})
    · intro t ht; exact hQ t ht
    · exact Set.infinite_univ.diff (Set.finite_singleton 0) |>.mono (fun t ht => by simpa using ht)
  have hd : ∀ d, ∑ m ∈ P.support.filter (fun m => e m = d), coeff m P = 0 := by
    intro d
    have := congrArg (fun q => Polynomial.coeff q d) hQ0
    simp only [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl (fun m _ => ?_)) this
    by_cases hm : e m = d
    · simp [hm]
    · simp [hm, Ne.symm hm]
  have := fiber_zero P.support (fun m => coeff m P) e hd (fun d => (d : K) - N)
  rw [← this]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm1 := hN m hm
  have : ((e m : ℕ) : K) = (m 0 : K) + N - m 1 := by
    simp only [e]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [this]; ring

theorem eval_Dd_one (q : Poly 2 K) :
    eval (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) K)) (Dd q) =
      ∑ ij : Fin 2 × Fin 2, J ij.1 ij.2 * eval (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) K)) (pderiv ij q) := by
  rw [eval_Dd]
  refine Finset.sum_congr rfl (fun kl _ => ?_)
  congr 1
  obtain ⟨k, l⟩ := kl
  fin_cases k <;> simp [Fin.sum_univ_two, Matrix.one_apply]

theorem tang [Infinite K] (hi : i * i = -1) (p : Poly 2 K)
    (hp : ∀ a : Matrix (Fin 2) (Fin 2) K, a 0 0 ^ 2 + a 0 1 ^ 2 = 1 → a 1 0 = -a 0 1 → a 1 1 = a 0 0 →
      eval (Function.uncurry a) p = 0) :
    ∑ ij : Fin 2 × Fin 2, J ij.1 ij.2 * eval (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) K)) (pderiv ij p) = 0 := by
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi
  set P := bind₁ (φv i) p
  have hz : ∀ t : K, t ≠ 0 → eval ![t, t⁻¹] P = 0 := by
    intro t ht
    have e := aeval_bind₁ (R := K) ![t, t⁻¹] (φv i) p
    rw [aeval_eq_eval] at e
    rw [e, aeval_eq_eval]
    have h2' : (2 : K) ≠ 0 := two_ne_zero
    set a : Matrix (Fin 2) (Fin 2) K := !![(t + t⁻¹) / 2, -(i / 2) * (t - t⁻¹); (i / 2) * (t - t⁻¹), (t + t⁻¹) / 2]
    have ha : (fun kl => eval ![t, t⁻¹] (φv i kl)) = Function.uncurry a := by
      funext kl
      obtain ⟨k, l⟩ := kl
      fin_cases k <;> fin_cases l <;> simp [φv, a] <;> ring
    rw [ha]
    apply hp
    · simp only [a, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      field_simp
      linear_combination ((t ^ 2 - 1) ^ 2) * hi
    · simp [a]
    · simp [a]
  have h0 := laur_zero P hz
  have h1 := Ee_iter_eval 1 P
  rw [relE_iter i hi, eval_mul, eval_C, eval_one_bind] at h1
  simp only [pow_one, Function.iterate_one] at h1
  rw [h0] at h1
  rw [← eval_Dd_one]
  have := (mul_eq_zero.1 h1).resolve_left (neg_ne_zero.2 hi0)
  exact this

end Bpart

theorem memT {F : Type*} [Field F] [Algebra F K] (a : GeometricGL 2 K) :
    a ∈ zeros (rotationEquations (F := F)) ↔
      ((a : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 + (a : Matrix (Fin 2) (Fin 2) K) 0 1 ^ 2 = 1 ∧
       (a : Matrix (Fin 2) (Fin 2) K) 1 0 = -(a : Matrix (Fin 2) (Fin 2) K) 0 1 ∧
       (a : Matrix (Fin 2) (Fin 2) K) 1 1 = (a : Matrix (Fin 2) (Fin 2) K) 0 0) := by
  simp only [zeros, rotationEquations, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, map_sub, map_add, map_pow, eval₂_X, map_one, eval₂_sub, eval₂_add,
    eval₂_pow, eval₂_one, unc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linear_combination h1, by linear_combination h2, by linear_combination -h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linear_combination h1, by linear_combination h2, by linear_combination -h3⟩

/-- the rotation group as a subgroup -/
def Tsub (F : Type*) [Field F] [Algebra F K] : Subgroup (GeometricGL 2 K) where
  carrier := zeros (rotationEquations (F := F))
  mul_mem' := by
    intro a b ha hb
    rw [memT] at ha hb ⊢
    obtain ⟨a1, a2, a3⟩ := ha
    obtain ⟨b1, b2, b3⟩ := hb
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [a2, a3, b2, b3]
    refine ⟨?_, by ring, by ring⟩
    linear_combination ((b : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 + (b : Matrix (Fin 2) (Fin 2) K) 0 1 ^ 2) * a1 + b1
  one_mem' := by
    rw [memT]; simp
  inv_mem' := by
    intro a ha
    have ha' := ha
    rw [memT] at ha
    obtain ⟨a1, a2, a3⟩ := ha
    set B : Matrix (Fin 2) (Fin 2) K := !![(a : Matrix (Fin 2) (Fin 2) K) 0 0, -(a : Matrix (Fin 2) (Fin 2) K) 0 1;
      (a : Matrix (Fin 2) (Fin 2) K) 0 1, (a : Matrix (Fin 2) (Fin 2) K) 0 0]
    have hB : (a : Matrix (Fin 2) (Fin 2) K) * B = 1 := by
      ext k l
      fin_cases k <;> fin_cases l <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two, a2, a3] <;>
        first | ring1 | linear_combination a1
    have hinv : ((a⁻¹ : GeometricGL 2 K) : Matrix (Fin 2) (Fin 2) K) = B := Units.inv_eq_of_mul_eq_one_right hB
    show a⁻¹ ∈ zeros (rotationEquations (F := F))
    rw [memT, hinv]
    simp [B]
    linear_combination a1

theorem mkUnit_aux (a : Matrix (Fin 2) (Fin 2) K) (h1 : a 0 0 ^ 2 + a 0 1 ^ 2 = 1) (h2 : a 1 0 = -a 0 1)
    (h3 : a 1 1 = a 0 0) : IsUnit a := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two, h2, h3]
  have : a 0 0 * a 0 0 - a 0 1 * -a 0 1 = 1 := by linear_combination h1
  rw [this]; exact isUnit_one

theorem x8_main {F K : Type*} [Field F] [CharZero F] [Field K] [Algebra F K] [IsAlgClosure F K] :
    (groupHull F K (Submodule.span F {(!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)}) : Set (GeometricGL 2 K)) =
      zeros (rotationEquations (F := F)) := by
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed F
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_eq_mul_self (-1 : K)
  have hi' : i * i = -1 := hi.symm
  have hJF : ∀ ij : Fin 2 × Fin 2, algebraMap F K ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) ij.1 ij.2)
      = J ij.1 ij.2 := by
    rintro ⟨k, l⟩; fin_cases k <;> fin_cases l <;> simp [J]
  have halg : IsAlgebraicGroup (Tsub (K := K) F) := by
    refine ⟨(MvPolynomial.map (algebraMap F K)) '' rotationEquations (F := F), ?_⟩
    ext a
    show a ∈ zeros (rotationEquations (F := F)) ↔ _
    simp only [zeros, Set.mem_setOf_eq, Set.forall_mem_image, eval₂_map]
    simp [Algebra.algebraMap_self]
  have htan : ((Submodule.span F {(!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)}) : Set _) ⊆
      tangentSet F (Tsub (K := K) F) := by
    intro X hX
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (SetLike.mem_coe.1 hX)
    intro p hp
    rw [mem_vI] at hp
    have := tang i hi' p (fun a h1 h2 h3 => by
      have hu := mkUnit_aux a h1 h2 h3
      have := hp hu.unit (by
        show hu.unit ∈ zeros (rotationEquations (F := F))
        rw [memT]; exact ⟨h1, h2, h3⟩)
      simpa using this)
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun ij _ => by rw [hJF ij]), this, mul_zero]
  apply Set.Subset.antisymm
  · intro a ha
    exact (sInf_le (Set.mem_insert_of_mem _ ⟨halg, htan⟩) : groupHull F K _ ≤ Tsub F) ha
  · intro a ha
    show a ∈ groupHull F K _
    refine (le_sInf ?_ : Tsub (K := K) F ≤ _) ha
    intro H hH
    rcases hH with rfl | ⟨⟨P, hP⟩, hL⟩
    · exact le_top
    intro b hb
    have hJ : ∀ p ∈ vanishingIdeal K (H : Set (GeometricGL 2 K)),
        ∑ ij : Fin 2 × Fin 2, J ij.1 ij.2 * eval (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) K))
          (pderiv ij p) = 0 := by
      intro p hp
      have := hL (Submodule.subset_span rfl) p hp
      rw [← this]
      exact Finset.sum_congr rfl (fun ij _ => by rw [hJF ij])
    have hb' := hb
    change b ∈ zeros (rotationEquations (F := F)) at hb'
    rw [memT] at hb'
    obtain ⟨b1, b2, b3⟩ := hb'
    have hmem : (b : GeometricGL 2 K) ∈ (H : Set (GeometricGL 2 K)) := by
      rw [hP]
      intro p hpP
      have hpI : p ∈ vanishingIdeal K (H : Set (GeometricGL 2 K)) := by
        rw [mem_vI]
        intro c hc
        rw [hP] at hc
        have := hc p hpP
        simpa [Algebra.algebraMap_self] using this
      have hD : ∀ k : ℕ, eval (Function.uncurry (1 : Matrix (Fin 2) (Fin 2) K)) ((Dd (K := K))^[k] p) = 0 := by
        intro k
        have hk : (Dd (K := K))^[k] p ∈ vanishingIdeal K (H : Set (GeometricGL 2 K)) := by
          induction k with
          | zero => simpa using hpI
          | succ k ih => rw [Function.iterate_succ_apply']; exact stab H hJ _ ih
        rw [mem_vI] at hk
        simpa using hk 1 H.one_mem
      have := vanish_on_T i hi' p hD _ b1 b2 b3
      simpa [Algebra.algebraMap_self] using this
    exact hmem

end QAlgorithms.Papers.Independent.Renew46.P22.X8RH

open QAlgorithms.Papers.Independent.Renew46.P22 in
theorem solution {F K : Type*} [Field F] [CharZero F] [Field K] [Algebra F K] [IsAlgClosure F K] :
    (groupHull F K (Submodule.span F {(!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)}) : Set (GeometricGL 2 K)) =
      zeros (rotationEquations (F := F)) :=
  QAlgorithms.Papers.Independent.Renew46.P22.X8RH.x8_main
