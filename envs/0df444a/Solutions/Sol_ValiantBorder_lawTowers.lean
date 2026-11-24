-- Prove2me | solution 1 for ValiantBorder.lawTowers
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:24:30.336729+00:00
-- url     : https://prove2.me/submissions/8aee7f04-0da4-44a4-a559-5a478778c0cd

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_towerRoutes
/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field* (2026),
`anthropics/formal-math` at revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5.
The finite-group tower construction, routes, local laws and estimates occur in
`Nc/Tower/{Base,Chain,Inst,Tower}.lean` and `Paper/Tree.lean`. Apache-2.0. -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The rings F₂[s]/(s^m)
-/

namespace Nc.Tower

open Polynomial

/-- The ring F₂[s]/(s^m). -/
def R (m : ℕ) : Type := (ZMod 2)[X] ⧸ Ideal.span {(X : (ZMod 2)[X]) ^ m}

noncomputable instance (m : ℕ) : CommRing (R m) :=
  inferInstanceAs (CommRing ((ZMod 2)[X] ⧸ Ideal.span {(X : (ZMod 2)[X]) ^ m}))

instance (m : ℕ) : Finite (R m) := by
  have : Module.Finite (ZMod 2) ((ZMod 2)[X] ⧸ Ideal.span {(X : (ZMod 2)[X]) ^ m}) :=
    (monic_X_pow m).finite_quotient
  exact Module.finite_of_finite (M := (ZMod 2)[X] ⧸ Ideal.span {(X : (ZMod 2)[X]) ^ m}) (ZMod 2)

noncomputable instance (m : ℕ) : Fintype (R m) := Fintype.ofFinite _

noncomputable instance (m : ℕ) : DecidableEq (R m) := Classical.decEq _

/-- The class of a polynomial. -/
noncomputable def mkR (m : ℕ) : (ZMod 2)[X] →+* R m := Ideal.Quotient.mk (Ideal.span {(X : (ZMod 2)[X]) ^ m})

theorem mkR_surjective (m : ℕ) : Function.Surjective (mkR m) := Ideal.Quotient.mk_surjective

theorem mkR_eq_zero {m : ℕ} {p : (ZMod 2)[X]} : mkR m p = 0 ↔ X ^ m ∣ p := by
  rw [← Ideal.mem_span_singleton]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Homomorphisms from the ring. -/
noncomputable def liftR {m : ℕ} {S : Type*} [CommRing S] (f : (ZMod 2)[X] →+* S) (hf : f (X ^ m) = 0) : R m →+* S :=
  Ideal.Quotient.lift (Ideal.span {(X : (ZMod 2)[X]) ^ m}) f (by
    intro p hp
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    rw [map_mul, hf, zero_mul])

theorem liftR_mk {m : ℕ} {S : Type*} [CommRing S] (f : (ZMod 2)[X] →+* S) (hf : f (X ^ m) = 0) (p : (ZMod 2)[X]) :
    liftR f hf (mkR m p) = f p := Ideal.Quotient.lift_mk _ _ _

/-- The constants. -/
noncomputable def cst (m : ℕ) : ZMod 2 →+* R m := (mkR m).comp C

theorem cst_apply (m : ℕ) (a : ZMod 2) : cst m a = mkR m (C a) := rfl

/-- The nilpotent element. -/
noncomputable def s (m : ℕ) : R m := mkR m X

theorem s_pow (m n : ℕ) : s m ^ n = mkR m (X ^ n) := by rw [s, map_pow]

theorem s_pow_self (m : ℕ) : s m ^ m = 0 := by rw [s_pow, mkR_eq_zero]

theorem s_pow_ge {m n : ℕ} (h : m ≤ n) : s m ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, s_pow_self, zero_mul]

theorem s_pow_ne {m n : ℕ} (h : n < m) : s m ^ n ≠ 0 := by
  rw [s_pow, Ne, mkR_eq_zero]
  intro hd
  have := Polynomial.degree_le_of_dvd hd (pow_ne_zero _ X_ne_zero)
  rw [degree_X_pow, degree_X_pow] at this
  have : m ≤ n := by exact_mod_cast this
  omega

theorem two_eq_zero (m : ℕ) : (2 : R m) = 0 := by
  have h : cst m 2 = 2 := map_ofNat _ 2
  rw [← h, show (2 : ZMod 2) = 0 from rfl, map_zero]

theorem add_self (m : ℕ) (x : R m) : x + x = 0 := by rw [← two_mul, two_eq_zero, zero_mul]

/-- Reduction modulo s^m. -/
noncomputable def red (m : ℕ) : R (m + 1) →+* R m :=
  liftR (mkR m) (by rw [mkR_eq_zero]; exact pow_dvd_pow X (Nat.le_succ m))

theorem red_mk (m : ℕ) (p : (ZMod 2)[X]) : red m (mkR (m + 1) p) = mkR m p := liftR_mk _ _ p

theorem red_s (m : ℕ) : red m (s (m + 1)) = s m := red_mk m X

theorem red_surjective (m : ℕ) : Function.Surjective (red m) := by
  intro x
  obtain ⟨p, rfl⟩ := mkR_surjective m x
  exact ⟨mkR (m + 1) p, red_mk m p⟩

/-- The kernel of the reduction. -/
theorem exists_of_red_eq_zero {m : ℕ} {x : R (m + 1)} (h : red m x = 0) :
    ∃ c : ZMod 2, x = cst (m + 1) c * s (m + 1) ^ m := by
  obtain ⟨p, rfl⟩ := mkR_surjective _ x
  rw [red_mk, mkR_eq_zero] at h
  obtain ⟨q, rfl⟩ := h
  refine ⟨q.coeff 0, ?_⟩
  have h1 : q = C (q.coeff 0) + X * q.divX := by
    rw [add_comm, mul_comm, divX_mul_X_add]
  have h2 : mkR (m + 1) (X ^ (m + 1)) = 0 := mkR_eq_zero.2 dvd_rfl
  rw [s_pow, cst_apply]
  conv_lhs => rw [h1, mul_add, ← mul_assoc, ← pow_succ, map_add, map_mul, map_mul _ (X ^ (m + 1)), h2, zero_mul,
    add_zero, mul_comm]

/-- The value at s = 0. -/
noncomputable def ev (m : ℕ) : R (m + 1) →+* ZMod 2 := liftR (Polynomial.evalRingHom 0) (by simp)

theorem ev_mk (m : ℕ) (p : (ZMod 2)[X]) : ev m (mkR (m + 1) p) = p.eval 0 := liftR_mk _ _ p

theorem ev_s (m : ℕ) : ev m (s (m + 1)) = 0 := by rw [s, ev_mk, eval_X]

theorem ev_cst (m : ℕ) (a : ZMod 2) : ev m (cst (m + 1) a) = a := by rw [cst_apply, ev_mk, eval_C]

/-- In F₂[s]/(s) every element is a constant. -/
theorem eq_cst_ev (x : R 1) : x = cst 1 (ev 0 x) := by
  obtain ⟨p, rfl⟩ := mkR_surjective _ x
  have h1 : p = C (p.coeff 0) + X * p.divX := by
    rw [add_comm, mul_comm, divX_mul_X_add]
  have h2 : mkR 1 X = 0 := by rw [mkR_eq_zero, pow_one]
  have h3 : ev 0 (mkR 1 p) = p.coeff 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact ev_mk 0 p
  rw [h3, cst_apply]
  conv_lhs => rw [h1, map_add, map_mul, h2, zero_mul, add_zero]

/-- The unit t = 1 + s. -/
noncomputable def t (m : ℕ) : R m := 1 + s m

theorem isUnit_t (m : ℕ) : IsUnit (t m) := by
  have h : IsNilpotent (s m) := ⟨m, s_pow_self m⟩
  exact h.isUnit_one_add

theorem red_t (m : ℕ) : red m (t (m + 1)) = t m := by rw [t, map_add, map_one, red_s]; rfl

theorem ev_t (m : ℕ) : ev m (t (m + 1)) = 1 := by rw [t, map_add, map_one, ev_s, add_zero]

theorem s_eq (m : ℕ) : s m = 1 + t m := by
  rw [t, ← add_assoc, add_self, zero_add]

end Nc.Tower

end
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The unitriangular group over F₂
-/

namespace Nc.Tower

open Matrix Finset

/-- The entries above the diagonal are free. -/
noncomputable def equivU (h : ℕ) : U h ≃ ({p : Fin h × Fin h // p.1 < p.2} → ZMod 2) where
  toFun A p := A.1.1 p.1.1 p.1.2
  invFun f := ⟨⟨Matrix.of fun i j => if hij : i < j then f ⟨(i, j), hij⟩ else if i = j then 1 else 0, by
      rw [Matrix.det_of_isUpperTriangular]
      · simp
      · intro i j hij
        have hij' : j < i := hij
        simp [not_lt_of_gt hij', hij'.ne']⟩, by
    intro i j
    refine ⟨fun hij => ?_, ?_⟩
    · simp [not_lt_of_gt hij, hij.ne']
    · simp⟩
  left_inv A := by
    refine Subtype.ext (Subtype.ext ?_)
    ext i j
    simp only [Matrix.of_apply]
    split_ifs with h1 h2
    · rfl
    · rw [h2]; exact ((A.2 j j).2).symm
    · exact ((A.2 i j).1 (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))).symm
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, hij⟩ := p
    have hij' : i < j := hij
    simp [hij']

theorem card_pairs (h : ℕ) : Fintype.card {p : Fin h × Fin h // p.1 < p.2} = h * (h - 1) / 2 := by
  rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
  have h1 : ∀ i : Fin h, (∑ j : Fin h, if i < j then 1 else 0) = h - 1 - i.1 := by
    intro i
    rw [← Finset.card_filter]
    have := Fin.card_Ioi i
    rw [← this]
    congr 1
    ext j
    simp
  rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_eq_sum_range (fun i => h - 1 - i),
    Finset.sum_range_reflect (fun i => i) h, Finset.sum_range_id]

/-- The order of U h. -/
theorem card_U (h : ℕ) : Fintype.card (U h) = 2 ^ (h * (h - 1) / 2) := by
  rw [Fintype.card_congr (equivU h), Fintype.card_fun, ZMod.card, card_pairs]

end Nc.Tower

end
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The groups SL_h(F₂[s]/(s^{n+1})) and their h unitriangular subgroups
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Matrix Finset

variable (h n : ℕ) [NeZero h]

/-- The group. -/
abbrev G : Type := Matrix.SpecialLinearGroup (Fin h) (R (n + 1))

/-- The unit t. -/
noncomputable def tu : (R (n + 1))ˣ := (isUnit_t (n + 1)).unit

theorem tu_val : ((tu n : (R (n + 1))ˣ) : R (n + 1)) = t (n + 1) := rfl

variable {h n}

/-- The weights of the shift by i: the places that were carried over. -/
noncomputable def wt (i a : Fin h) : (R (n + 1))ˣ := if a < i then (tu n)⁻¹ else 1

/-- Conjugation by the i-th power of the shift. -/
noncomputable def shMat (i : Fin h) (A : Matrix (Fin h) (Fin h) (ZMod 2)) : Matrix (Fin h) (Fin h) (R (n + 1)) :=
  diagonal (fun a => ((wt i a : (R (n + 1))ˣ) : R (n + 1))) *
    ((A.map (cst (n + 1))).submatrix (Equiv.subRight i) (Equiv.subRight i) *
      diagonal (fun a => (((wt i a)⁻¹ : (R (n + 1))ˣ) : R (n + 1))))

theorem shMat_apply (i : Fin h) (A : Matrix (Fin h) (Fin h) (ZMod 2)) (a b : Fin h) :
    (shMat i A : Matrix (Fin h) (Fin h) (R (n + 1))) a b =
      (wt i a : (R (n + 1))ˣ) * (cst (n + 1) (A (a - i) (b - i)) * ((wt i b)⁻¹ : (R (n + 1))ˣ)) := by
  rw [shMat, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rfl

theorem shMat_one (i : Fin h) : (shMat i 1 : Matrix (Fin h) (Fin h) (R (n + 1))) = 1 := by
  ext a b
  rw [shMat_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · have : a - i ≠ b - i := fun e => hab (sub_left_injective e)
    rw [Matrix.one_apply_ne this, Matrix.one_apply_ne hab]
    simp

theorem shMat_mul (i : Fin h) (A B : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (shMat i (A * B) : Matrix (Fin h) (Fin h) (R (n + 1))) = shMat i A * shMat i B := by
  ext a b
  rw [shMat_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [shMat_apply]
  rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight i) _ _ fun c => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, map_mul]
  have := Units.inv_mul (wt i (c + i) : (R (n + 1))ˣ)
  linear_combination (-(wt i a : (R (n + 1))ˣ) * cst (n + 1) (A (a - i) c) *
    cst (n + 1) (B c (b - i)) * ((wt i b)⁻¹ : (R (n + 1))ˣ) : R (n + 1)) * this

theorem det_shMat (i : Fin h) (A : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (shMat i A : Matrix (Fin h) (Fin h) (R (n + 1))).det = cst (n + 1) A.det := by
  rw [shMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Matrix.det_submatrix_equiv_self, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have : (∏ a, ((wt i a : (R (n + 1))ˣ) : R (n + 1))) * ∏ a, (((wt i a)⁻¹ : (R (n + 1))ˣ) : R (n + 1)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => Units.mul_inv _
  linear_combination (cst (n + 1) A.det) * this

/-- The embedding of SL_h(F₂) shifted by i. -/
noncomputable def th0 (i : Fin h) : SL2 h →* G h n where
  toFun A := ⟨shMat i A.1, by rw [det_shMat, A.2, map_one]⟩
  map_one' := Subtype.ext (shMat_one i)
  map_mul' A B := Subtype.ext (shMat_mul i A.1 B.1)

theorem th0_val (i : Fin h) (A : SL2 h) : (th0 i A : G h n).1 = shMat i A.1 := rfl

/-- The value at s = 0. -/
noncomputable def evG : G h n →* SL2 h := Matrix.SpecialLinearGroup.map (ev n)

theorem evG_apply (g : G h n) (a b : Fin h) : (evG g).1 a b = ev n (g.1 a b) := rfl

theorem ev_wt (i a : Fin h) : ev n ((wt i a : (R (n + 1))ˣ) : R (n + 1)) = 1 := by
  rw [wt]
  split_ifs
  · have h1 : ev n ((tu n : (R (n + 1))ˣ) : R (n + 1)) = 1 := ev_t n
    have h2 := congrArg (ev n) (Units.mul_inv (tu n))
    rw [map_mul, h1, one_mul, map_one] at h2
    exact h2
  · simp

theorem ev_wt_inv (i a : Fin h) : ev n (((wt i a)⁻¹ : (R (n + 1))ˣ) : R (n + 1)) = 1 := by
  have h2 := congrArg (ev n) (Units.mul_inv (wt i a : (R (n + 1))ˣ))
  rw [map_mul, ev_wt, one_mul, map_one] at h2
  exact h2

theorem evG_th0 (i : Fin h) (A : SL2 h) (a b : Fin h) : (evG (th0 i A : G h n)).1 a b = A.1 (a - i) (b - i) := by
  rw [evG_apply, th0_val, shMat_apply, map_mul, map_mul, ev_wt, ev_wt_inv, ev_cst, one_mul, mul_one]

theorem evG_th0_injective (i : Fin h) : Function.Injective fun A : SL2 h => evG (th0 i A : G h n) := by
  intro A B e
  refine Subtype.ext ?_
  ext a b
  have := congrFun (congrFun (congrArg Subtype.val e) (a + i)) (b + i)
  simp only at this
  rw [evG_th0, evG_th0, add_sub_cancel_right, add_sub_cancel_right] at this
  exact this

/-- The h unitriangular subgroups. -/
noncomputable def th (i : Fin h) : U h →* G h n := (th0 i).comp (U h).subtype

theorem th_injective (i : Fin h) : Function.Injective (th i : U h →* G h n) := by
  intro A B e
  exact Subtype.ext (evG_th0_injective (n := n) i (congrArg evG e))

theorem evG_th_eq_one {i : Fin h} {u : U h} (e : evG (th i u : G h n) = 1) : u = 1 := by
  refine Subtype.ext (evG_th0_injective (n := n) i ?_)
  simp only
  have h1 : (th i u : G h n) = th0 i u.1 := rfl
  rw [← h1, e]
  simp

variable (n) in
/-- The entry of the generators. -/
noncomputable def tt (k : Fin h) : R (n + 1) := if k = 0 then t (n + 1) else 1

theorem sub_one_ne (h2 : 2 ≤ h) (k : Fin h) : k - 1 ≠ k := by
  intro e
  have : (1 : Fin h) = 0 := by
    have := congrArg (fun x => k - x) e
    simpa using this
  have := congrArg Fin.val this
  rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- The generators: involutions of type k. -/
noncomputable def gen (h2 : 2 ≤ h) (k : Fin h) : G h n :=
  ⟨transvection (k - 1) k (tt n k), det_transvection_of_ne _ _ (sub_one_ne h2 k) _⟩

theorem gen_val (h2 : 2 ≤ h) (k : Fin h) : (gen h2 k : G h n).1 = transvection (k - 1) k (tt n k) := rfl

theorem gen_mul_self (h2 : 2 ≤ h) (k : Fin h) : (gen h2 k : G h n) * gen h2 k = 1 := by
  refine Subtype.ext ((transvection_mul_transvection_same _ _ (sub_one_ne h2 k) (tt n k) (tt n k)).trans ?_)
  rw [add_self, transvection_zero]
  rfl

/-- The type i + 1 + l. -/
def sh (i : Fin h) (l : Fin (h - 1)) : Fin h := hi l + i

theorem sh_sub_one (h2 : 2 ≤ h) (i : Fin h) (l : Fin (h - 1)) : sh i l - 1 = lo l + i := by
  have : (hi l : Fin h) = lo l + 1 := by
    refine Fin.ext ?_
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
    have := l.2
    simp only [lo, hi]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [sh, this]
  abel

theorem sh_ne (i : Fin h) (l : Fin (h - 1)) : sh i l ≠ i := by
  intro e
  have h1 : (hi l : Fin h) = 0 := by simpa [sh] using e
  have := congrArg Fin.val h1
  simp [hi] at this

theorem sh_injective (i : Fin h) : Function.Injective (sh i) := by
  intro l l' e
  have h1 : (hi l : Fin h) = hi l' := by simpa [sh] using e
  have := congrArg Fin.val h1
  simp only [hi] at this
  exact Fin.ext (by omega)

theorem exists_sh {i k : Fin h} (hk : k ≠ i) : ∃ l, sh i l = k := by
  have h1 : (k - i).1 ≠ 0 := by
    intro e
    exact hk (sub_eq_zero.1 (Fin.ext e))
  have h3 := (k - i).2
  refine ⟨⟨(k - i).1 - 1, by omega⟩, ?_⟩
  have : (hi ⟨(k - i).1 - 1, by omega⟩ : Fin h) = k - i := by
    refine Fin.ext ?_
    simp only [hi]
    omega
  rw [sh, this, sub_add_cancel]

theorem wt_sub_one (h2 : 2 ≤ h) {i k : Fin h} (hk : k ≠ i) :
    ((wt i (k - 1) : (R (n + 1))ˣ) : R (n + 1)) * ((wt i k)⁻¹ : (R (n + 1))ˣ) = tt n k := by
  by_cases h0 : k = 0
  · subst h0
    have hi0 : (0 : Fin h) < i := Fin.pos_iff_ne_zero.2 hk.symm
    have hl : ¬ ((0 : Fin h) - 1 < i) := by
      intro hlt
      have h1 : ((0 : Fin h) - 1).1 = h - 1 := by
        rw [zero_sub, Fin.val_neg']
        rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega), Nat.mod_eq_of_lt (by omega)]
      have h2' := Fin.lt_def.1 hlt
      have := i.2
      omega
    rw [wt, wt, if_neg hl, if_pos hi0, tt, if_pos rfl, inv_inv, Units.val_one, one_mul, tu_val]
  · have h1 : (k - 1).1 = k.1 - 1 := by
      have hk0 : 0 < k.1 := Nat.pos_of_ne_zero fun e => h0 (Fin.ext e)
      have h3 : (1 : Fin h) ≤ k := by
        rw [Fin.le_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
        exact hk0
      rw [Fin.sub_val_of_le h3, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
    have hk0 : 0 < k.1 := Nat.pos_of_ne_zero fun e => h0 (Fin.ext e)
    have hki : k.1 ≠ i.1 := fun e => hk (Fin.ext e)
    have h2' : k - 1 < i ↔ k < i := by
      rw [Fin.lt_def, Fin.lt_def, h1]
      omega
    rw [wt, wt, tt, if_neg h0]
    by_cases hlt : k < i
    · rw [if_pos (h2'.2 hlt), if_pos hlt]
      exact Units.mul_inv _
    · rw [if_neg (fun e => hlt (h2'.1 e)), if_neg hlt]
      simp

/-- The simple root elements of the i-th unitriangular subgroup are generators. -/
theorem th_x (h2 : 2 ≤ h) (i : Fin h) (l : Fin (h - 1)) : (th i (x h l) : G h n) = gen h2 (sh i l) := by
  refine Subtype.ext ?_
  have e1 : (th i (x h l) : G h n).1 = shMat i (1 + Matrix.single (lo l) (hi l) 1) := rfl
  rw [e1, gen_val, transvection, sh_sub_one h2]
  ext a b
  rw [shMat_apply, Matrix.add_apply, Matrix.add_apply]
  by_cases hab : a = b
  · subst hab
    have h1 : ¬ (lo l = a - i ∧ hi l = a - i) := fun e => lo_ne_hi l (e.1.trans e.2.symm)
    have h3 : ¬ (lo l + i = a ∧ sh i l = a) := by
      rintro ⟨e1, e2⟩
      have : lo l + i = hi l + i := e1.trans e2.symm
      exact lo_ne_hi l (add_right_cancel this)
    rw [Matrix.single_apply, Matrix.single_apply, if_neg h1, if_neg h3]
    simp
  · have h4 : a - i ≠ b - i := fun e => hab (sub_left_injective e)
    rw [Matrix.one_apply_ne h4, Matrix.one_apply_ne hab, zero_add, zero_add]
    by_cases h1 : lo l = a - i ∧ hi l = b - i
    · have ha : lo l + i = a := by rw [h1.1, sub_add_cancel]
      have hb : sh i l = b := by rw [sh, h1.2, sub_add_cancel]
      rw [h1.1, h1.2, Matrix.single_apply_same, map_one, one_mul, sub_add_cancel, hb, Matrix.single_apply_same]
      have := wt_sub_one (n := n) h2 (sh_ne i l)
      rw [sh_sub_one h2, ha, hb] at this
      exact this
    · have h3 : ¬ (lo l + i = a ∧ sh i l = b) := by
        rintro ⟨e1, e2⟩
        exact h1 ⟨by rw [← e1, add_sub_cancel_right], by rw [← e2, sh, add_sub_cancel_right]⟩
      rw [Matrix.single_apply, Matrix.single_apply, if_neg h1, if_neg h3]
      simp

end Nc.Tower

end
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The layers 1 + s^{n+1} A
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Matrix Finset

variable {h n : ℕ} [NeZero h]

/-- Reduction of the groups. -/
noncomputable def redG : G h (n + 1) →* G h n := Matrix.SpecialLinearGroup.map (red (n + 1))

theorem redG_apply (g : G h (n + 1)) (a b : Fin h) : (redG g).1 a b = red (n + 1) (g.1 a b) := rfl

theorem s_sq (n : ℕ) : (s (n + 2) ^ (n + 1)) ^ 2 = 0 := by
  rw [← pow_mul]
  exact s_pow_ge (by omega)

/-- The matrix 1 + s^{n+1} A. -/
noncomputable def layMat (n : ℕ) (A : Matrix (Fin h) (Fin h) (ZMod 2)) : Matrix (Fin h) (Fin h) (R (n + 2)) :=
  1 + s (n + 2) ^ (n + 1) • A.map (cst (n + 2))

theorem det_layMat (A : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (layMat n A).det = 1 + cst (n + 2) A.trace * s (n + 2) ^ (n + 1) := by
  rw [layMat, Matrix.det_one_add_smul, s_sq, mul_zero, add_zero]
  congr 2
  simp [Matrix.trace, map_sum]

theorem layMat_mul (A B : Matrix (Fin h) (Fin h) (ZMod 2)) : layMat n A * layMat n B = layMat n (A + B) := by
  have h1 : s (n + 2) ^ (n + 1) * s (n + 2) ^ (n + 1) = 0 := by rw [← sq, s_sq]
  rw [layMat, layMat, layMat, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm, h1,
    zero_smul, add_zero, Matrix.map_add _ (map_add _), smul_add]
  abel

/-- The element 1 + s^{n+1} A. -/
noncomputable def lay (A : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) : G h (n + 1) :=
  ⟨layMat n A, by rw [det_layMat, hA, map_zero, zero_mul, add_zero]⟩

theorem lay_val (A : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) : (lay (n := n) A hA).1 = layMat n A := rfl

theorem lay_mul (A B : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) (hB : B.trace = 0) :
    lay (n := n) A hA * lay B hB = lay (A + B) (by rw [trace_add, hA, hB, add_zero]) :=
  Subtype.ext (layMat_mul A B)

theorem layMat_injective : Function.Injective (layMat (h := h) n) := by
  intro A B e
  ext a b
  have h1 := congrFun (congrFun e a) b
  simp only [layMat, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h1
  have h2 := add_left_cancel h1
  have key : ∀ x : ZMod 2, s (n + 2) ^ (n + 1) * cst (n + 2) x = 0 → x = 0 := by
    intro x hx
    fin_cases x
    · rfl
    · exfalso
      have : cst (n + 2) 1 = 1 := map_one _
      change s (n + 2) ^ (n + 1) * cst (n + 2) 1 = 0 at hx
      rw [this, mul_one] at hx
      exact s_pow_ne (by omega) hx
  have h3 := key (A a b - B a b) (by rw [map_sub, mul_sub, h2, sub_self])
  exact sub_eq_zero.1 h3

theorem red_s_pow (n : ℕ) : red (n + 1) (s (n + 2) ^ (n + 1)) = 0 := by
  rw [map_pow, red_s]
  exact s_pow_self _

theorem redG_lay (A : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) : redG (lay (n := n) A hA) = 1 := by
  refine Subtype.ext ?_
  ext a b
  rw [redG_apply, lay_val, layMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, red_s_pow,
    zero_mul, add_zero]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.one_apply_ne hab, map_zero]
    exact (Matrix.one_apply_ne hab).symm

/-- The kernel of the reduction is the layer. -/
theorem exists_lay {g : G h (n + 1)} (hg : redG g = 1) : ∃ A hA, g = lay A hA := by
  have h1 : ∀ a b, ∃ c : ZMod 2, g.1 a b = (1 : Matrix (Fin h) (Fin h) (R (n + 2))) a b +
      s (n + 2) ^ (n + 1) * cst (n + 2) c := by
    intro a b
    have h2 : red (n + 1) (g.1 a b - (1 : Matrix (Fin h) (Fin h) (R (n + 2))) a b) = 0 := by
      rw [map_sub, ← redG_apply, hg]
      by_cases hab : a = b
      · subst hab
        simp
      · rw [Matrix.one_apply_ne hab, map_zero, sub_zero]
        exact Matrix.one_apply_ne hab
    obtain ⟨c, hc⟩ := exists_of_red_eq_zero h2
    refine ⟨c, ?_⟩
    rw [mul_comm, ← hc]
    abel
  choose A hA using h1
  have e : g.1 = layMat n (Matrix.of A) := by
    ext a b
    rw [hA, layMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rfl
  have htr : (Matrix.of A).trace = 0 := by
    have h2 := g.2
    rw [e, det_layMat] at h2
    have h3 : cst (n + 2) (Matrix.of A).trace * s (n + 2) ^ (n + 1) = 0 := by
      have := congrArg (fun x => x - 1) h2
      simpa using this
    by_contra hne
    have h4 : (Matrix.of A).trace = 1 := by
      generalize (Matrix.of A).trace = x at hne
      fin_cases x
      · exact absurd rfl hne
      · rfl
    rw [h4, map_one, one_mul] at h3
    exact s_pow_ne (by omega) h3
  exact ⟨Matrix.of A, htr, Subtype.ext e⟩

/-- The reduction is onto. -/
theorem redG_surjective : Function.Surjective (redG : G h (n + 1) →* G h n) := by
  intro g
  choose f hf using red_surjective (n + 1)
  let A : Matrix (Fin h) (Fin h) (R (n + 2)) := g.1.map f
  have hA : A.map (red (n + 1)) = g.1 := by
    ext a b
    simp [A, hf]
  have hd : red (n + 1) A.det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, g.2]
  have hdd : A.det * A.det = 1 := by
    obtain ⟨c, hc⟩ := exists_of_red_eq_zero (m := n + 1) (x := A.det - 1) (by rw [map_sub, hd, map_one, sub_self])
    have h1 : A.det = 1 + cst (n + 2) c * s (n + 2) ^ (n + 1) := by rw [← hc]; ring
    have h2 := s_sq n
    have h3 := two_eq_zero (n + 2)
    rw [h1]
    linear_combination (cst (n + 2) c) ^ 2 * h2 +
      (cst (n + 2) c * s (n + 2) ^ (n + 1)) * h3
  let i0 : Fin h := 0
  let B : Matrix (Fin h) (Fin h) (R (n + 2)) := A.updateRow i0 (A.det • A i0)
  have hB : B.det = 1 := by
    rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, hdd]
  refine ⟨(⟨B, hB⟩ : G h (n + 1)), Subtype.ext ?_⟩
  ext a b
  refine (redG_apply (⟨B, hB⟩ : G h (n + 1)) a b).trans ?_
  have h4 : red (n + 1) (A a b) = g.1 a b := congrFun (congrFun hA a) b
  by_cases ha : a = i0
  · subst ha
    simp only [B, Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul, map_mul, hd, one_mul, h4]
  · simp only [B, Matrix.updateRow_ne ha, h4]

/-- The trace-zero matrices. -/
def tr0 (h : ℕ) : AddSubgroup (Matrix (Fin h) (Fin h) (ZMod 2)) := (Matrix.traceAddMonoidHom (Fin h) (ZMod 2)).ker

theorem card_tr0 : Nat.card (tr0 h) = 2 ^ (h ^ 2 - 1) := by
  have h1 := AddSubgroup.card_mul_index (tr0 h)
  have h2 : (tr0 h).index = 2 := by
    rw [tr0, AddSubgroup.index_ker]
    have : (Matrix.traceAddMonoidHom (Fin h) (ZMod 2)).range = ⊤ := by
      rw [AddMonoidHom.range_eq_top]
      intro c
      refine ⟨Matrix.single 0 0 c, ?_⟩
      simp
    rw [this, AddSubgroup.card_top, Nat.card_zmod]
  have h3 : Nat.card (Matrix (Fin h) (Fin h) (ZMod 2)) = 2 ^ (h ^ 2) := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Fin h → Fin h → ZMod 2) = _
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    rw [← pow_mul, sq]
  rw [h2, h3] at h1
  have hpos : 1 ≤ h ^ 2 := Nat.one_le_pow _ _ (NeZero.pos h)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hpos
  rw [hk, pow_add, pow_one] at h1
  rw [hk, Nat.add_sub_cancel_left]
  omega

theorem card_ker_redG : Nat.card (redG : G h (n + 1) →* G h n).ker = 2 ^ (h ^ 2 - 1) := by
  rw [← card_tr0]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun A : tr0 h => ⟨lay A.1 A.2, redG_lay A.1 A.2⟩) ⟨?_, ?_⟩)
  · intro A B e
    have := congrArg (fun g : (redG : G h (n + 1) →* G h n).ker => g.1.1) e
    exact Subtype.ext (layMat_injective this)
  · rintro ⟨g, hg⟩
    obtain ⟨A, hA, rfl⟩ := exists_lay hg
    exact ⟨⟨A, hA⟩, rfl⟩

theorem card_G_succ : Nat.card (G h (n + 1)) = Nat.card (G h n) * 2 ^ (h ^ 2 - 1) := by
  have h1 := Subgroup.card_mul_index (redG : G h (n + 1) →* G h n).ker
  rw [card_ker_redG, Subgroup.index_ker, MonoidHom.range_eq_top.2 redG_surjective, Subgroup.card_top] at h1
  rw [← h1, mul_comm]

theorem evG_bijective_zero : Function.Bijective (evG : G h 0 →* SL2 h) := by
  constructor
  · intro g g' e
    refine Subtype.ext ?_
    ext a b
    rw [eq_cst_ev (g.1 a b), eq_cst_ev (g'.1 a b)]
    congr 1
    exact congrFun (congrFun (congrArg Subtype.val e) a) b
  · intro A
    refine ⟨th0 0 A, Subtype.ext ?_⟩
    ext a b
    rw [evG_th0, sub_zero, sub_zero]

theorem evG_surjective : Function.Surjective (evG : G h n →* SL2 h) := by
  intro A
  refine ⟨th0 0 A, Subtype.ext ?_⟩
  ext a b
  rw [evG_th0, sub_zero, sub_zero]

/-- The order of the group. -/
theorem card_G (h n : ℕ) [NeZero h] : Nat.card (G h n) = Nat.card (SL2 h) * 2 ^ ((h ^ 2 - 1) * n) := by
  induction n with
  | zero =>
    rw [mul_zero, pow_zero, mul_one]
    exact Nat.card_congr (Equiv.ofBijective _ evG_bijective_zero)
  | succ n ih => rw [card_G_succ, ih, mul_assoc, ← pow_add, mul_add, mul_one]

/-- The kernel of the value at s = 0 is a 2-group. -/
theorem card_ker_evG : Nat.card (evG : G h n →* SL2 h).ker = 2 ^ ((h ^ 2 - 1) * n) := by
  have h1 := Subgroup.card_mul_index (evG : G h n →* SL2 h).ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 evG_surjective, Subgroup.card_top, card_G, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

end Nc.Tower

end
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The chain of subgroups
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

variable {h n : ℕ} [NeZero h]

/-- The kernel of the value at s = 0. -/
noncomputable def Ker (h n : ℕ) [NeZero h] : Subgroup (G h n) := (evG : G h n →* SL2 h).ker

theorem mem_Ker {g : G h n} : g ∈ Ker h n ↔ evG g = 1 := Iff.rfl

/-- **Paper: Section sec:tower.** "Let K_n be the kernel of s ↦ 0; it is a 2-group of order 2^((h²−1)n)." -/
theorem _root_.Paper.prop_tower_kernel (h n : ℕ) [NeZero h] :
    IsPGroup 2 (Ker h n) ∧ Nat.card (Ker h n) = 2 ^ ((h ^ 2 - 1) * n) :=
  ⟨IsPGroup.of_card card_ker_evG, card_ker_evG⟩




/-- The number of steps of the tower. -/
def JJ (h n : ℕ) : ℕ := (h ^ 2 - 1) * n / ee h

theorem exists_chain (h n : ℕ) [NeZero h] : ∃ Γ : ℕ → Subgroup (G h n), Γ 0 = ⊥ ∧ (∀ j, Γ j ≤ Γ (j + 1)) ∧
    (∀ j, Γ j ≤ Ker h n) ∧ ∀ j ≤ JJ h n, Nat.card (Γ j) = (2 ^ ee h) ^ j := by
  classical
  have step : ∀ j, ∀ H : Subgroup (Ker h n), Nat.card H = 2 ^ (ee h * j) → j < JJ h n →
      ∃ H' : Subgroup (Ker h n), Nat.card H' = 2 ^ (ee h * (j + 1)) ∧ H ≤ H' := by
    intro j H hH hj
    refine Sylow.exists_subgroup_card_pow_prime_le 2 ?_ H hH (Nat.mul_le_mul_left _ (Nat.le_succ j))
    rw [(Paper.prop_tower_kernel h n).2]
    refine pow_dvd_pow 2 ?_
    calc ee h * (j + 1) ≤ ee h * JJ h n := Nat.mul_le_mul_left _ hj
      _ ≤ _ := Nat.mul_div_le _ _
  have h0 : Nat.card (⊥ : Subgroup (Ker h n)) = 2 ^ (ee h * min 0 (JJ h n)) := by simp
  have step' : ∀ j, ∀ H : {H : Subgroup (Ker h n) // Nat.card H = 2 ^ (ee h * min j (JJ h n))},
      ∃ H' : {H : Subgroup (Ker h n) // Nat.card H = 2 ^ (ee h * min (j + 1) (JJ h n))}, H.1 ≤ H'.1 := by
    intro j H
    by_cases hj : j < JJ h n
    · obtain ⟨H', h1, h2⟩ := step j H.1 (by rw [H.2, min_eq_left hj.le]) hj
      exact ⟨⟨H', by rw [h1, min_eq_left (Nat.succ_le_of_lt hj)]⟩, h2⟩
    · refine ⟨⟨H.1, ?_⟩, le_rfl⟩
      rw [H.2, min_eq_right (not_lt.1 hj), min_eq_right ((not_lt.1 hj).trans (Nat.le_succ j))]
  choose nxt hnxt using step'
  let f : (j : ℕ) → {H : Subgroup (Ker h n) // Nat.card H = 2 ^ (ee h * min j (JJ h n))} := fun j =>
    Nat.rec ⟨⊥, h0⟩ nxt j
  have hf : ∀ j, (f j).1 ≤ (f (j + 1)).1 := fun j => hnxt j (f j)
  refine ⟨fun j => (f j).1.map (Ker h n).subtype, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_bot _
  · exact fun j => Subgroup.map_mono (hf j)
  · intro j g hg
    obtain ⟨k, -, rfl⟩ := hg
    exact k.2
  · intro j hj
    rw [Nat.card_congr ((f j).1.equivMapOfInjective _ (Subgroup.subtype_injective _)).toEquiv.symm, (f j).2,
      min_eq_left hj, pow_mul]

end Nc.Tower

end
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Coordinates
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

/-- Coordinates for the left action of a subgroup. -/
theorem exists_coord {P Q : Type*} [Group P] [Group Q] (φ : P →* Q) (hφ : Function.Injective φ) :
    ∃ co : Q → P, ∀ p q, co (φ p * q) = p * co q := by
  let r : Setoid Q :=
    { r := fun q q' => ∃ p, q' = φ p * q
      iseqv := ⟨fun q => ⟨1, by simp⟩, fun {q q'} ⟨p, hp⟩ => ⟨p⁻¹, by rw [hp, map_inv, inv_mul_cancel_left]⟩,
        fun {q q' q''} ⟨p, hp⟩ ⟨p', hp'⟩ => ⟨p' * p, by rw [hp', hp, map_mul, mul_assoc]⟩⟩ }
  have h1 : ∀ q : Q, ∃ p, q = φ p * (Quotient.mk r q).out := fun q => Quotient.exact (Quotient.out_eq (Quotient.mk r q))
  choose co hco using h1
  refine ⟨co, fun p q => ?_⟩
  apply hφ
  have h2 : Quotient.mk r (φ p * q) = Quotient.mk r q := (Quotient.sound (s := r) ⟨p, rfl⟩ : Quotient.mk r q = _).symm
  have h3 := hco (φ p * q)
  rw [h2] at h3
  have h4 := hco q
  have h5 : φ (co (φ p * q)) * (Quotient.mk r q).out = φ p * (φ (co q) * (Quotient.mk r q).out) := by
    rw [← h3, ← h4]
  rw [← mul_assoc] at h5
  rw [map_mul]
  exact mul_right_cancel h5

variable {h n : ℕ} [NeZero h]

/-- The image of the i-th unitriangular subgroup in SL_h(F₂). -/
noncomputable def thQ (i : Fin h) : U h →* SL2 h := (evG : G h 0 →* SL2 h).comp (th i)

theorem evG_th (i : Fin h) (u : U h) : evG (th i u : G h n) = thQ i u := by
  refine Subtype.ext ?_
  ext a b
  rw [thQ]
  change (evG (th0 i u.1 : G h n)).1 a b = (evG (th0 i u.1 : G h 0)).1 a b
  rw [evG_th0, evG_th0]

theorem thQ_injective (i : Fin h) : Function.Injective (thQ i : U h →* SL2 h) := by
  intro u v e
  exact Subtype.ext (evG_th0_injective (n := 0) i e)

/-- The coordinate of an element of SL_h(F₂) at its vertex of type i. -/
noncomputable def coQ (i : Fin h) : SL2 h → U h := (exists_coord (thQ i) (thQ_injective i)).choose

theorem coQ_mul (i : Fin h) (u : U h) (q : SL2 h) : coQ i (thQ i u * q) = u * coQ i q :=
  (exists_coord (thQ i) (thQ_injective i)).choose_spec u q

theorem exists_other (h2 : 2 ≤ h) (k : Fin h) : ∃ i : Fin h, k ≠ i := by
  by_contra hc
  push Not at hc
  have h1 := hc (k - 1)
  exact sub_one_ne h2 k h1.symm

theorem gen_ne (h2 : 2 ≤ h) (k : Fin h) : evG (gen h2 k : G h n) ≠ 1 := by
  obtain ⟨i, hi⟩ := exists_other h2 k
  obtain ⟨l, rfl⟩ := exists_sh hi
  rw [← th_x h2 i l]
  intro e
  exact x_ne_one l (evG_th_eq_one e)

/-- The first chambers of the pairs of type k. -/
theorem exists_firstQ (h2 : 2 ≤ h) (k : Fin h) :
    ∃ F : SL2 h → Prop, ∀ q, F (evG (gen h2 k : G h 0) * q) ↔ ¬ F q := by
  refine exists_first _ (fun q => ?_) fun q e => ?_
  · rw [← mul_assoc, ← map_mul, gen_mul_self, map_one, one_mul]
  · exact gen_ne (n := 0) h2 k (by simpa using e)

/-- The first chambers of the pairs of type k. -/
def FQ (h2 : 2 ≤ h) (k : Fin h) : SL2 h → Prop := (exists_firstQ h2 k).choose

theorem evG_gen (h2 : 2 ≤ h) (k : Fin h) : evG (gen h2 k : G h n) = evG (gen h2 k : G h 0) := by
  obtain ⟨i, hi⟩ := exists_other h2 k
  obtain ⟨l, rfl⟩ := exists_sh hi
  rw [← th_x h2 i l, ← th_x h2 i l, evG_th, evG_th]

theorem FQ_iff (h2 : 2 ≤ h) (k : Fin h) (q : SL2 h) : FQ h2 k (evG (gen h2 k : G h n) * q) ↔ ¬ FQ h2 k q := by
  rw [evG_gen]
  exact (exists_firstQ h2 k).choose_spec q

theorem FU_iff (l : Fin (h - 1)) (u : U h) : FU l (x h l * u) ↔ ¬ FU l u := (exists_firstU l).choose_spec u

end Nc.Tower

end
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The tower
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Finset

variable (h n : ℕ) [NeZero h]

/-- The chain of subgroups. -/
noncomputable def Gam : ℕ → Subgroup (G h n) := (exists_chain h n).choose

theorem Gam_zero : Gam h n 0 = ⊥ := (exists_chain h n).choose_spec.1

theorem Gam_le (j : ℕ) : Gam h n j ≤ Gam h n (j + 1) := (exists_chain h n).choose_spec.2.1 j

theorem Gam_ker (j : ℕ) : Gam h n j ≤ Ker h n := (exists_chain h n).choose_spec.2.2.1 j

theorem card_Gam {j : ℕ} (hj : j ≤ JJ h n) : Nat.card (Gam h n j) = (2 ^ ee h) ^ j :=
  (exists_chain h n).choose_spec.2.2.2 j hj

/-- The chambers. -/
abbrev XX (j : ℕ) : Type := G h n ⧸ Gam h n j

noncomputable instance instFintypeXX (j : ℕ) : Fintype (XX h n j) := Fintype.ofFinite _

noncomputable instance instDecXX (j : ℕ) : DecidableEq (XX h n j) := Classical.decEq _

variable {h n}

/-- The value of a chamber in SL_h(F₂). -/
noncomputable def evX {j : ℕ} : XX h n j → SL2 h :=
  Quotient.lift (fun g => evG g) (by
    intro a b hab
    have h1 : a⁻¹ * b ∈ Gam h n j := QuotientGroup.leftRel_apply.1 hab
    have h2 := mem_Ker.1 (Gam_ker h n j h1)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2)

theorem evX_mk {j : ℕ} (g : G h n) : evX (QuotientGroup.mk g : XX h n j) = evG g := rfl

theorem evX_smul {j : ℕ} (g : G h n) (c : XX h n j) : evX (g • c) = evG g * evX c := by
  induction c using QuotientGroup.induction_on with
  | H a =>
    change evX (QuotientGroup.mk (g * a) : XX h n j) = _
    rw [evX_mk, map_mul]
    rfl

/-- The covering. -/
noncomputable def pr {j : ℕ} : XX h n j → XX h n (j + 1) := Subgroup.quotientMapOfLE (Gam_le h n j)

/-- **Paper: Proposition prop:tower.** The projections are equivariant. -/
theorem _root_.Paper.prop_tower_equivariant {j : ℕ} (g : G h n) (c : XX h n j) : pr (g • c) = g • pr c := by
  induction c using QuotientGroup.induction_on with
  | H a => rfl

theorem evX_pr {j : ℕ} (c : XX h n j) : evX (pr c) = evX c := by
  induction c using QuotientGroup.induction_on with
  | H a => rfl

/-- The coordinate at the vertex of type i. -/
noncomputable def cor {j : ℕ} (i : Fin h) (c : XX h n j) : U h := coQ i (evX c)

theorem cor_th {j : ℕ} (i : Fin h) (u : U h) (c : XX h n j) : cor i ((th i u : G h n) • c) = u * cor i c := by
  rw [cor, cor, evX_smul, evG_th, coQ_mul]

theorem cor_pr {j : ℕ} (i : Fin h) (c : XX h n j) : cor i (pr c) = cor i c := by rw [cor, cor, evX_pr]

variable (h n) in
/-- The vertices of type i: the chambers with coordinate 1. -/
abbrev VV (j : ℕ) (i : Fin h) : Type := {c : XX h n j // cor i c = 1}

noncomputable instance instFintypeVV (j : ℕ) (i : Fin h) : Fintype (VV h n j i) := Fintype.ofFinite _

noncomputable instance instDecVV (j : ℕ) (i : Fin h) : DecidableEq (VV h n j i) := Classical.decEq _

/-- The vertex of a chamber. -/
noncomputable def vert {j : ℕ} (i : Fin h) (c : XX h n j) : VV h n j i :=
  ⟨(th i (cor i c)⁻¹ : G h n) • c, by rw [cor_th, inv_mul_cancel]⟩

theorem vert_val {j : ℕ} (i : Fin h) (c : XX h n j) : (vert i c).1 = (th i (cor i c)⁻¹ : G h n) • c := rfl

theorem th_vert {j : ℕ} (i : Fin h) (c : XX h n j) : (th i (cor i c) : G h n) • (vert i c).1 = c := by
  rw [vert_val, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

theorem vert_th {j : ℕ} (i : Fin h) (u : U h) (c : XX h n j) : vert i ((th i u : G h n) • c) = vert i c := by
  refine Subtype.ext ?_
  rw [vert_val, vert_val, cor_th, ← mul_smul, ← map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

theorem vert_of {j : ℕ} (i : Fin h) (v : VV h n j i) : vert i v.1 = v := by
  refine Subtype.ext ?_
  rw [vert_val, v.2, inv_one, map_one, one_smul]

theorem vert_cor_bijective (j : ℕ) (i : Fin h) : Function.Bijective fun c : XX h n j => (vert i c, cor i c) := by
  constructor
  · intro c c' e
    simp only [Prod.mk.injEq] at e
    rw [← th_vert i c, ← th_vert i c', e.1, e.2]
  · rintro ⟨v, u⟩
    refine ⟨(th i u : G h n) • v.1, ?_⟩
    simp only
    rw [vert_th, vert_of, cor_th, v.2, mul_one]

variable (h n) in
/-- The edges: pairs of type k, represented by their first chambers. -/
abbrev EE (h2 : 2 ≤ h) (j : ℕ) : Type := {p : Fin h × XX h n j // FQ h2 p.1 (evX p.2)}

noncomputable instance instFintypeEE (h2 : 2 ≤ h) (j : ℕ) : Fintype (EE h n h2 j) := Fintype.ofFinite _

noncomputable instance instDecEE (h2 : 2 ≤ h) (j : ℕ) : DecidableEq (EE h n h2 j) := Classical.decEq _

theorem FQ_gen {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) :
    FQ h2 k (evX ((gen h2 k : G h n) • c)) ↔ ¬ FQ h2 k (evX c) := by rw [evX_smul, FQ_iff]

theorem gen_gen {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) :
    (gen h2 k : G h n) • (gen h2 k : G h n) • c = c := by rw [← mul_smul, gen_mul_self, one_smul]

/-- **Paper: Proposition prop:tower(a).** The copy of U_h "acts freely on every X^(j)". -/
theorem _root_.Paper.prop_tower_free {j : ℕ} (i : Fin h) (u : U h) (c : XX h n j) (e : (th i u : G h n) • c = c) :
    u = 1 := by
  have h1 := congrArg (cor i) e
  rwa [cor_th, mul_eq_right] at h1

/-- **Paper: Proposition prop:tower(b).** "c and X_i c always lie in different i-cosets." -/
theorem _root_.Paper.prop_tower_cosets {j : ℕ} (h2 : 2 ≤ h) (i : Fin h) (c : XX h n j) (u : U h) :
    (th i u : G h n) • c ≠ (gen h2 i : G h n) • c := by
  intro e
  have h1 := congrArg evX e
  rw [evX_smul, evX_smul, mul_left_inj] at h1
  -- the entry (i−1, i) at s = 0
  have hi : (i - 1 : Fin h) ≠ i := sub_one_ne h2 i
  have h2' := congrArg (fun M : SL2 h => M.1 (i - 1) i) h1
  simp only [th, MonoidHom.comp_apply, evG_th0] at h2'
  rw [evG_apply, gen_val] at h2'
  simp [Matrix.transvection, Matrix.one_apply_ne hi, tt] at h2'
  rw [(u.2 _ _).1 (Fin.pos_iff_ne_zero.2 fun h0 => hi (by rw [neg_eq_zero.1 h0, sub_zero]))] at h2'
  split_ifs at h2' <;> simp [ev_t] at h2'

theorem gen_smul_ne {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) : (gen h2 k : G h n) • c ≠ c := fun e =>
  Paper.prop_tower_cosets h2 k c 1 (by rw [map_one, one_smul, e])

/-- The edge of type k at a chamber. -/
noncomputable def edge {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) : EE h n h2 j :=
  open Classical in
  if hc : FQ h2 k (evX c) then ⟨(k, c), hc⟩ else ⟨(k, (gen h2 k : G h n) • c), (FQ_gen h2 k c).2 hc⟩

theorem edge_type {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) : (edge h2 k c).1.1 = k := by
  unfold edge
  split_ifs <;> rfl

theorem edge_end {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) :
    (edge h2 k c).1.2 = c ∨ (edge h2 k c).1.2 = (gen h2 k : G h n) • c := by
  unfold edge
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem edge_self {j : ℕ} (h2 : 2 ≤ h) (e : EE h n h2 j) : edge h2 e.1.1 e.1.2 = e := by
  unfold edge
  rw [dif_pos e.2]

theorem edge_gen {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) : edge h2 k ((gen h2 k : G h n) • c) = edge h2 k c := by
  unfold edge
  by_cases hc : FQ h2 k (evX c)
  · rw [dif_pos hc, dif_neg (fun e => (FQ_gen h2 k c).1 e hc)]
    exact Subtype.ext (Prod.ext rfl (gen_gen h2 k c))
  · rw [dif_neg hc, dif_pos ((FQ_gen h2 k c).2 hc)]

/-- The edges of one type are half of the chambers. -/
theorem card_edges (h2 : 2 ≤ h) (j : ℕ) (i : Fin h) :
    2 * (univ.filter fun e : EE h n h2 j => e.1.1 = i).card = 1 * Fintype.card (XX h n j) := by
  classical
  have h1 : (univ.filter fun e : EE h n h2 j => e.1.1 = i).card =
      (univ.filter fun c : XX h n j => FQ h2 i (evX c)).card := by
    refine Finset.card_bij' (fun e _ => e.1.2) (fun c _ => edge h2 i c) ?_ ?_ ?_ ?_
    · intro e he
      rw [mem_filter] at he ⊢
      exact ⟨mem_univ _, he.2 ▸ e.2⟩
    · intro c _
      rw [mem_filter]
      exact ⟨mem_univ _, edge_type h2 i c⟩
    · intro e he
      rw [mem_filter] at he
      rw [← he.2]
      exact edge_self h2 e
    · intro c hc
      rw [mem_filter] at hc
      unfold edge
      rw [dif_pos hc.2]
  have h3 : (univ.filter fun c : XX h n j => FQ h2 i (evX c)).card =
      (univ.filter fun c : XX h n j => ¬ FQ h2 i (evX c)).card := by
    refine Finset.card_bij' (fun c _ => (gen h2 i : G h n) • c) (fun c _ => (gen h2 i : G h n) • c) ?_ ?_ ?_ ?_
    · intro c hc
      rw [mem_filter] at hc ⊢
      exact ⟨mem_univ _, fun e => (FQ_gen h2 i c).1 e hc.2⟩
    · intro c hc
      rw [mem_filter] at hc ⊢
      exact ⟨mem_univ _, (FQ_gen h2 i c).2 hc.2⟩
    · intro c _; exact gen_gen h2 i c
    · intro c _; exact gen_gen h2 i c
  have h4 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (XX h n j))) (fun c => FQ h2 i (evX c))
  rw [Finset.card_univ] at h4
  rw [h1, one_mul]
  omega

theorem deg_edges (h2 : 2 ≤ h) (j : ℕ) (c : XX h n j) (i : Fin h) :
    (univ.filter fun e : EE h n h2 j => e.1.1 = i ∧ (e.1.2 = c ∨ (gen h2 e.1.1 : G h n) • e.1.2 = c)).card ≤ 1 := by
  rw [Finset.card_le_one]
  have key : ∀ e ∈ univ.filter fun e : EE h n h2 j => e.1.1 = i ∧ (e.1.2 = c ∨ (gen h2 e.1.1 : G h n) • e.1.2 = c),
      e = edge h2 i c := by
    intro e he
    rw [mem_filter] at he
    obtain ⟨-, h1, h3 | h3⟩ := he
    · rw [← h1, ← h3, edge_self]
    · rw [← h1, ← h3, edge_gen, edge_self]
  intro e he e' he'
  rw [key e he, key e' he']

/-- The near pair {u, x_l u}. -/
noncomputable def npair (l : Fin (h - 1)) (u : U h) : NN h :=
  open Classical in if hu : FU l u then ⟨(l, u), hu⟩ else ⟨(l, x h l * u), (FU_iff l u).2 hu⟩

theorem npair_type (l : Fin (h - 1)) (u : U h) : (npair l u).1.1 = l := by
  unfold npair
  split_ifs <;> rfl

theorem npair_sym (l : Fin (h - 1)) (u : U h) :
    s(u, x h l * u) = s((npair l u).1.2, x h (npair l u).1.1 * (npair l u).1.2) := by
  unfold npair
  split_ifs
  · rfl
  · simp only
    rw [← mul_assoc, x_mul_self, one_mul, Sym2.eq_swap]

theorem npair_eq {l : Fin (h - 1)} {u u' : U h} (e : npair l u = npair l u') : u = u' ∨ u = x h l * u' := by
  unfold npair at e
  split_ifs at e with h1 h3 h3
  · exact Or.inl (congrArg (fun p => p.1.2) e)
  · exact Or.inr (congrArg (fun p => p.1.2) e)
  · right
    have h4 : x h l * u = u' := congrArg (fun p => p.1.2) e
    rw [← h4, ← mul_assoc, x_mul_self, one_mul]
  · left
    have h4 : x h l * u = x h l * u' := congrArg (fun p => p.1.2) e
    exact mul_left_cancel h4

theorem npair_self (ν : NN h) : npair ν.1.1 ν.1.2 = ν := by
  unfold npair
  rw [dif_pos ν.2]

theorem npair_x (l : Fin (h - 1)) (u : U h) : npair l (x h l * u) = npair l u := by
  unfold npair
  by_cases hu : FU l u
  · rw [dif_pos hu, dif_neg (fun e => (FU_iff l u).1 e hu)]
    refine Subtype.ext (Prod.ext rfl ?_)
    simp only
    rw [← mul_assoc, x_mul_self, one_mul]
  · rw [dif_neg hu, dif_pos ((FU_iff l u).2 hu)]

/-- The index of a type seen from the type i. -/
noncomputable def idx (i k : Fin h) (hk : k ≠ i) : Fin (h - 1) := (exists_sh hk).choose

theorem sh_idx (i k : Fin h) (hk : k ≠ i) : sh i (idx i k hk) = k := (exists_sh hk).choose_spec

theorem idx_sh (i : Fin h) (l : Fin (h - 1)) : idx i (sh i l) (sh_ne i l) = l :=
  sh_injective i (sh_idx i _ _)

theorem gen_idx (h2 : 2 ≤ h) (i k : Fin h) (hk : k ≠ i) : (gen h2 k : G h n) = th i (x h (idx i k hk)) := by
  rw [th_x h2, sh_idx]

/-- The edges of types other than i are the near pairs at the vertices of type i. -/
noncomputable def nearFun (h2 : 2 ≤ h) (j : ℕ) (i : Fin h) (e : {e : EE h n h2 j // e.1.1 ≠ i}) : VV h n j i × NN h :=
  (vert i e.1.1.2, npair (idx i e.1.1.1 e.2) (cor i e.1.1.2))

theorem nearFun_bijective (h2 : 2 ≤ h) (j : ℕ) (i : Fin h) : Function.Bijective (nearFun (n := n) h2 j i) := by
  constructor
  · rintro ⟨⟨⟨k, c⟩, hc⟩, hk⟩ ⟨⟨⟨k', c'⟩, hc'⟩, hk'⟩ e
    simp only [nearFun, Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    have hl : idx i k hk = idx i k' hk' := by
      have h6 : (npair (idx i k hk) (cor i c)).1.1 = (npair (idx i k' hk') (cor i c')).1.1 :=
        congrArg (fun p : NN h => p.1.1) e2
      rw [npair_type, npair_type] at h6
      exact h6
    have hkk : k = k' := by rw [← sh_idx i k hk, hl, sh_idx]
    subst hkk
    have hcc : c = c' := by
      rcases npair_eq e2 with e3 | e3
      · exact (vert_cor_bijective j i).1 (Prod.ext e1 e3)
      · exfalso
        have h3 : c = (gen h2 k : G h n) • c' := by
          refine (vert_cor_bijective j i).1 (Prod.ext ?_ ?_)
          · simp only
            rw [gen_idx h2 i k hk, vert_th, e1]
          · simp only
            rw [gen_idx h2 i k hk, cor_th, e3]
        have h4 : FQ h2 k (evX c) := hc
        rw [h3] at h4
        exact (FQ_gen h2 k c').1 h4 hc'
    subst hcc
    rfl
  · rintro ⟨v, ν⟩
    let l := ν.1.1
    let c : XX h n j := (th i ν.1.2 : G h n) • v.1
    have hk : sh i l ≠ i := sh_ne i l
    refine ⟨⟨edge h2 (sh i l) c, by rw [edge_type]; exact hk⟩, ?_⟩
    have h5 : ∀ (k : Fin h) (hk' : k ≠ i), k = sh i l → idx i k hk' = l := by
      rintro k hk' rfl
      exact idx_sh i l
    have hg : (gen h2 (sh i l) : G h n) = th i (x h l) := (th_x h2 i l).symm
    refine Prod.ext ?_ ?_
    · change vert i (edge h2 (sh i l) c).1.2 = v
      rcases edge_end h2 (sh i l) c with e | e
      · rw [e, vert_th, vert_of]
      · rw [e, hg, vert_th, vert_th, vert_of]
    · change npair (idx i (edge h2 (sh i l) c).1.1 _) (cor i (edge h2 (sh i l) c).1.2) = ν
      rw [h5 _ _ (edge_type h2 (sh i l) c)]
      rcases edge_end h2 (sh i l) c with e | e
      · rw [e, cor_th, v.2, mul_one]
        exact npair_self ν
      · rw [e, hg, cor_th, npair_x, cor_th, v.2, mul_one]
        exact npair_self ν

/-- The covering on edges. -/
noncomputable def prE {j : ℕ} (h2 : 2 ≤ h) (e : EE h n h2 j) : EE h n h2 (j + 1) :=
  ⟨(e.1.1, pr e.1.2), by rw [evX_pr]; exact e.2⟩

/-- The covering on vertices. -/
noncomputable def prV {j : ℕ} {i : Fin h} (v : VV h n j i) : VV h n (j + 1) i := ⟨pr v.1, by rw [cor_pr, v.2]⟩

theorem vert_pr {j : ℕ} (i : Fin h) (c : XX h n j) : vert i (pr c) = prV (vert i c) := by
  refine Subtype.ext ?_
  rw [vert_val, cor_pr, ← Paper.prop_tower_equivariant]
  rfl

theorem card_XX {j : ℕ} (hj : j ≤ JJ h n) : Fintype.card (XX h n j) * (2 ^ ee h) ^ j = Nat.card (G h n) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Gam h n j), card_Gam h n hj, Nat.card_eq_fintype_card]

theorem card_XX_succ {j : ℕ} (hj : j < JJ h n) :
    Fintype.card (XX h n j) = 2 ^ ee h * Fintype.card (XX h n (j + 1)) := by
  have h1 := card_XX (h := h) (n := n) hj.le
  have h3 := card_XX (h := h) (n := n) (Nat.succ_le_of_lt hj)
  have hp : 0 < (2 ^ ee h) ^ j := Nat.pow_pos (Nat.pow_pos (by omega))
  refine Nat.eq_of_mul_eq_mul_right hp ?_
  rw [h1, ← h3, Nat.succ_eq_add_one, pow_succ]
  ring

/-- **Paper: Proposition prop:tower.** The projections "are b to one". -/
theorem _root_.Paper.prop_tower_fibre {j : ℕ} (hj : j < JJ h n) (d : XX h n (j + 1)) :
    (univ.filter fun c : XX h n j => pr c = d).card = 2 ^ ee h := by
  classical
  have h1 : ∀ (g : G h n) (d : XX h n (j + 1)), (univ.filter fun c : XX h n j => pr c = d).card =
      (univ.filter fun c : XX h n j => pr c = g • d).card := by
    intro g d
    refine Finset.card_bij' (fun c _ => g • c) (fun c _ => g⁻¹ • c) ?_ ?_ ?_ ?_
    · intro c hc
      rw [mem_filter] at hc ⊢
      exact ⟨mem_univ _, by rw [Paper.prop_tower_equivariant, hc.2]⟩
    · intro c hc
      rw [mem_filter] at hc ⊢
      exact ⟨mem_univ _, by rw [Paper.prop_tower_equivariant, hc.2, inv_smul_smul]⟩
    · intro c _; exact inv_smul_smul g c
    · intro c _; exact smul_inv_smul g c
  have h3 : ∀ d' : XX h n (j + 1), (univ.filter fun c : XX h n j => pr c = d').card =
      (univ.filter fun c : XX h n j => pr c = d).card := by
    intro d'
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (G h n) d' d
    exact h1 g d'
  have h4 : Fintype.card (XX h n j) = ∑ d' : XX h n (j + 1), (univ.filter fun c : XX h n j => pr c = d').card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun c _ => mem_univ _
  rw [Finset.sum_congr rfl fun d' _ => h3 d', Finset.sum_const, Finset.card_univ, smul_eq_mul, card_XX_succ hj,
    mul_comm] at h4
  exact (Nat.eq_of_mul_eq_mul_left (Fintype.card_pos_iff.2 ⟨d⟩) h4).symm

theorem fibre_edges {j : ℕ} (h2 : 2 ≤ h) (hj : j < JJ h n) (d : EE h n h2 (j + 1)) :
    (univ.filter fun e : EE h n h2 j => prE h2 e = d).card ≤ 2 ^ ee h := by
  rw [← Paper.prop_tower_fibre hj d.1.2]
  refine Finset.card_le_card_of_injOn (fun e => e.1.2) ?_ ?_
  · intro e he
    rw [Finset.mem_coe, mem_filter] at he ⊢
    exact ⟨mem_univ _, congrArg (fun p : EE h n h2 (j + 1) => p.1.2) he.2⟩
  · intro e he e' he' hee
    rw [Finset.mem_coe, mem_filter] at he he'
    have h1 : e.1.1 = e'.1.1 := by
      have a1 := congrArg (fun p : EE h n h2 (j + 1) => p.1.1) he.2
      have a2 := congrArg (fun p : EE h n h2 (j + 1) => p.1.1) he'.2
      exact a1.trans a2.symm
    exact Subtype.ext (Prod.ext h1 hee)

/-- **Paper: Proposition prop:tower(b).** "Exactly b of them onto each": b cosets over each, a coset being given by its
one element in VV (prop_tower_representatives). -/
theorem _root_.Paper.prop_tower_cosets_over {j : ℕ} {i : Fin h} (hj : j < JJ h n) (v : VV h n (j + 1) i) :
    (univ.filter fun w : VV h n j i => prV w = v).card = 2 ^ ee h := by
  rw [← Paper.prop_tower_fibre hj v.1]
  refine Finset.card_bij (fun w _ => w.1) (fun w hw => mem_filter.2 ⟨mem_univ _, congrArg Subtype.val (mem_filter.1 hw).2⟩)
    (fun w _ w' _ e => Subtype.ext e) (fun c hc => ⟨⟨c, ?_⟩, mem_filter.2 ⟨mem_univ _, Subtype.ext (mem_filter.1 hc).2⟩, rfl⟩)
  rw [← cor_pr, (mem_filter.1 hc).2]
  exact v.2

/-- **Paper: Proposition prop:tower(a).** "We call its orbits i-cosets": every i-coset has one element in VV. -/
theorem _root_.Paper.prop_tower_representatives {j : ℕ} (i : Fin h) (c : XX h n j) :
    ∃! v : VV h n j i, ∃ u : U h, (th i u : G h n) • v.1 = c := by
  refine ⟨vert i c, ⟨cor i c, th_vert i c⟩, ?_⟩
  rintro v ⟨u, rfl⟩
  rw [vert_th, vert_of]

/-- Hosts. -/
theorem exists_host (j : ℕ) (i : Fin h) : ∃ f : VV h n j i → XX h n (j + 1), j < JJ h n →
    Function.Injective f ∧ ∀ v, vert i (f v) = prV v := by
  classical
  by_cases hj : j < JJ h n
  · have h1 : ∀ d : VV h n (j + 1) i, Nonempty ({v : VV h n j i // prV v = d} ↪ U h) := by
      intro d
      refine Function.Embedding.nonempty_of_card_le ?_
      rw [card_U, ← ee, ← Paper.prop_tower_cosets_over hj d, Fintype.card_subtype]
    let φ : ∀ d : VV h n (j + 1) i, {v : VV h n j i // prV v = d} ↪ U h := fun d => (h1 d).some
    have hφ : ∀ (v : VV h n j i) (d : VV h n (j + 1) i) (hv : prV v = d), φ (prV v) ⟨v, rfl⟩ = φ d ⟨v, hv⟩ := by
      rintro v _ rfl
      rfl
    refine ⟨fun v => (th i (φ (prV v) ⟨v, rfl⟩) : G h n) • (prV v).1, fun _ => ⟨?_, fun v => ?_⟩⟩
    · intro v v' e
      simp only at e
      have e1 : prV v = prV v' := by
        have := congrArg (vert i) e
        rwa [vert_th, vert_th, vert_of, vert_of] at this
      have e2 : φ (prV v) ⟨v, rfl⟩ = φ (prV v') ⟨v', rfl⟩ := by
        have := congrArg (cor i) e
        rwa [cor_th, cor_th, (prV v).2, (prV v').2, mul_one, mul_one] at this
      rw [hφ v (prV v') e1] at e2
      exact congrArg Subtype.val ((φ (prV v')).injective e2)
    · rw [vert_th, vert_of]
  · exact ⟨fun v => pr v.1, fun hj' => absurd hj' hj⟩

end Nc.Tower

end
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Short words

Every element of the group is a product of at most C (n + 1)^7 generators.
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Matrix Finset

/-- The last index. -/
def last (h : ℕ) [NeZero h] : Fin h := ⟨h - 1, Nat.sub_lt (NeZero.pos h) Nat.one_pos⟩

variable {h n : ℕ} [NeZero h] (h2 : 2 ≤ h)

/-- The element is a product of at most N generators. -/
def WL (g : G h n) (N : ℕ) : Prop := ∃ l : List (Fin h), l.length ≤ N ∧ (l.map (gen h2)).prod = g

variable {h2}

theorem WL.mono {g : G h n} {N M : ℕ} (hg : WL h2 g N) (hM : N ≤ M) : WL h2 g M := by
  obtain ⟨l, h1, h3⟩ := hg
  exact ⟨l, h1.trans hM, h3⟩

theorem WL.one : WL h2 (1 : G h n) 0 := ⟨[], le_rfl, rfl⟩

theorem WL.gen (k : Fin h) : WL h2 (gen h2 k : G h n) 1 := ⟨[k], le_rfl, by simp⟩

theorem WL.mul {g g' : G h n} {N M : ℕ} (hg : WL h2 g N) (hg' : WL h2 g' M) : WL h2 (g * g') (N + M) := by
  obtain ⟨l, h1, rfl⟩ := hg
  obtain ⟨l', h3, rfl⟩ := hg'
  exact ⟨l ++ l', by simp; omega, by simp⟩

/-- Elementary matrices. -/
noncomputable def El (i j : Fin h) (hij : i ≠ j) (y : R (n + 1)) : G h n :=
  ⟨transvection i j y, det_transvection_of_ne _ _ hij y⟩

theorem El_val (i j : Fin h) (hij : i ≠ j) (y : R (n + 1)) : (El i j hij y).1 = transvection i j y := rfl

theorem El_add (i j : Fin h) (hij : i ≠ j) (y y' : R (n + 1)) :
    El i j hij y * El i j hij y' = El i j hij (y + y') :=
  Subtype.ext (transvection_mul_transvection_same _ _ hij y y')

theorem two_nsmul_mat (M : Matrix (Fin h) (Fin h) (R (n + 1))) : M + M = 0 := by
  ext a b
  exact add_self _ _

/-- The commutator. -/
theorem El_comm (i j k : Fin h) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j) (y y' : R (n + 1)) :
    El i k hik y * El k j hkj y' * (El i k hik y * El k j hkj y') = El i j hij (y * y') := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, El_val, transvection]
  set a := Matrix.single i k y with ha
  set b := Matrix.single k j y' with hb
  have haa : a * a = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hik.symm _
  have hbb : b * b = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hkj.symm _
  have hba : b * a = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _
  have hab : a * b = Matrix.single i j (y * y') := Matrix.single_mul_single_same _ _ _ _ _
  rw [← hab]
  have e1 : (1 + a) * (1 + b) * ((1 + a) * (1 + b)) = 1 + a * b + ((a + b + a * b) + (a + b + a * b)) +
      (a * a + a * a * b + b * a + b * b + b * a * b + a * (b * a) + a * (b * b) + a * (b * a) * b) := by
    noncomm_ring
  rw [e1, two_nsmul_mat, haa, hba, hbb]
  simp

theorem WL.comm {i j k : Fin h} {hik : i ≠ k} {hkj : k ≠ j} (hij : i ≠ j) {y y' : R (n + 1)} {N M : ℕ}
    (h1 : WL h2 (El i k hik y) N) (h3 : WL h2 (El k j hkj y') M) : WL h2 (El i j hij (y * y')) (2 * (N + M)) := by
  rw [← El_comm i j k hik hkj hij]
  exact ((h1.mul h3).mul (h1.mul h3)).mono (by omega)

theorem gen_eq_El (k : Fin h) : (gen h2 k : G h n) = El (k - 1) k (sub_one_ne h2 k) (tt n k) := rfl

/-- Constant elementary matrices above the diagonal. -/
theorem WL.upper (d : ℕ) (i j : Fin h) (hij : i ≠ j) (hd : i.1 + (d + 1) = j.1) :
    WL h2 (El i j hij 1 : G h n) (4 ^ d) := by
  induction d generalizing j with
  | zero =>
    have hj : j ≠ 0 := by
      intro e
      rw [e] at hd
      simp at hd
    have h1 : j - 1 = i := by
      refine Fin.ext ?_
      have h3 : (1 : Fin h) ≤ j := by
        rw [Fin.le_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
        omega
      rw [Fin.sub_val_of_le h3, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
      omega
    have h3 := WL.gen (n := n) (h2 := h2) j
    rw [gen_eq_El, tt, if_neg hj] at h3
    subst h1
    exact h3
  | succ d ih =>
    let k : Fin h := ⟨j.1 - 1, by omega⟩
    have hk : k.1 = j.1 - 1 := rfl
    have hik : i ≠ k := by
      intro e
      have := congrArg Fin.val e
      omega
    have hkj : k ≠ j := by
      intro e
      have := congrArg Fin.val e
      omega
    have h1 := ih k hik (by omega)
    have h3 : WL h2 (El k j hkj 1 : G h n) 1 := by
      have hj : j ≠ 0 := by
        intro e
        rw [e] at hd
        simp at hd
      have h4 : j - 1 = k := by
        refine Fin.ext ?_
        have h5 : (1 : Fin h) ≤ j := by
          rw [Fin.le_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
          omega
        rw [Fin.sub_val_of_le h5, Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega)]
      have h6 := WL.gen (n := n) (h2 := h2) j
      rw [gen_eq_El, tt, if_neg hj] at h6
      have h7 : (El (j - 1) j (sub_one_ne h2 j) 1 : G h n) = El k j hkj 1 := by
        refine Subtype.ext ?_
        rw [El_val, El_val, h4]
      rwa [h7] at h6
    have h4 := h1.comm hij h3
    rw [one_mul] at h4
    refine h4.mono ?_
    have : 1 ≤ 4 ^ d := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    omega

theorem WL.upper' (i j : Fin h) (hij : i < j) : WL h2 (El i j hij.ne 1 : G h n) (4 ^ h) := by
  have hlt := Fin.lt_def.1 hij
  refine (WL.upper (j.1 - i.1 - 1) i j hij.ne (by omega)).mono (Nat.pow_le_pow_right (by omega) ?_)
  have := j.2
  omega

theorem zero_sub_one (h2 : 2 ≤ h) : (0 : Fin h) - 1 = last h := by
  refine Fin.ext ?_
  rw [zero_sub, Fin.val_neg', Fin.val_one', Nat.mod_eq_of_lt (show 1 < h by omega), Nat.mod_eq_of_lt (by omega)]
  rfl

theorem lt_last {i : Fin h} (hi : i ≠ last h) : i < last h := by
  rw [Fin.lt_def]
  have h1 := i.2
  have h3 : i.1 ≠ h - 1 := fun e => hi (Fin.ext e)
  simp only [last]
  omega

theorem zero_ne_last (h2 : 2 ≤ h) : last h ≠ 0 := by
  intro e
  have := congrArg Fin.val e
  simp [last] at this
  omega

theorem exists_third (h3 : 3 ≤ h) (i j : Fin h) : ∃ k, i ≠ k ∧ k ≠ j := by
  by_contra hc
  push Not at hc
  have h1 : (univ : Finset (Fin h)) ⊆ {i, j} := by
    intro k _
    by_cases e : i = k
    · simp [e]
    · simp [hc k e]
  have h4 := Finset.card_le_card h1
  rw [Finset.card_univ, Fintype.card_fin] at h4
  have h5 : ({i, j} : Finset (Fin h)).card ≤ 2 := Finset.card_le_two
  omega

/-- All elementary matrices with entry t. -/
theorem WL.el_t (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) :
    WL h2 (El i j hij (t (n + 1)) : G h n) (4 ^ (h + 3)) := by
  have hp : 1 ≤ 4 ^ h := Nat.one_le_pow _ _ (by omega)
  have e1 : 4 ^ (h + 1) = 4 * 4 ^ h := by ring
  have e2 : 4 ^ (h + 2) = 16 * 4 ^ h := by ring
  have e3 : 4 ^ (h + 3) = 64 * 4 ^ h := by ring
  have hL0 := zero_ne_last (h := h) h2
  have c1 : WL h2 (El (last h) 0 hL0 (t (n + 1)) : G h n) 1 := by
    have h6 := WL.gen (n := n) (h2 := h2) 0
    rw [gen_eq_El, tt, if_pos rfl] at h6
    have h7 : (El (0 - 1) 0 (sub_one_ne h2 0) (t (n + 1)) : G h n) = El (last h) 0 hL0 (t (n + 1)) := by
      refine Subtype.ext ?_
      rw [El_val, El_val, zero_sub_one h2]
    rwa [h7] at h6
  have c2 : ∀ j (hj : last h ≠ j), WL h2 (El (last h) j hj (t (n + 1)) : G h n) (4 ^ (h + 1)) := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0
      exact c1.mono (by omega)
    · have h4 := c1.comm hj (WL.upper' (n := n) (h2 := h2) 0 j (Fin.pos_iff_ne_zero.2 h0))
      rw [mul_one] at h4
      exact h4.mono (by omega)
  have c3 : ∀ i j (hij : i ≠ j), i ≠ last h → j ≠ last h → WL h2 (El i j hij (t (n + 1)) : G h n) (4 ^ (h + 2)) := by
    intro i j hij hi hj
    have h4 := (WL.upper' (n := n) (h2 := h2) i (last h) (lt_last hi)).comm hij (c2 j hj.symm)
    rw [one_mul] at h4
    exact h4.mono (by omega)
  by_cases hi : i = last h
  · subst hi
    exact (c2 j hij).mono (by omega)
  · by_cases hj : j = last h
    · subst hj
      obtain ⟨k, hk1, hk2⟩ := exists_third h3 i (last h)
      have h4 := (c3 i k hk1 hi hk2).comm hij (WL.upper' (n := n) (h2 := h2) k (last h) (lt_last hk2))
      rw [mul_one] at h4
      exact h4.mono (by omega)
    · exact (c3 i j hij hi hj).mono (by omega)

/-- Powers of the entry. -/
theorem WL.el_pow (h3 : 3 ≤ h) {y : R (n + 1)} {B : ℕ} (hy : ∀ i j (hij : i ≠ j), WL h2 (El i j hij y : G h n) B)
    (m : ℕ) (hm : 1 ≤ m) (i j : Fin h) (hij : i ≠ j) : WL h2 (El i j hij (y ^ m) : G h n) (B * m ^ 3) := by
  induction m using Nat.strong_induction_on generalizing i j with
  | _ m ih =>
    rcases Nat.eq_or_lt_of_le hm with h1 | h1
    · subst h1
      simpa using hy i j hij
    · obtain ⟨k, hk1, hk2⟩ := exists_third h3 i j
      have hab : m / 2 + (m - m / 2) = m := by omega
      have p1 := ih (m / 2) (by omega) (by omega) i k hk1
      have p2 := ih (m - m / 2) (by omega) (by omega) k j hk2
      have p3 := p1.comm hij p2
      rw [← pow_add, hab] at p3
      refine p3.mono ?_
      generalize ha : m / 2 = a at *
      generalize hb : m - a = b at *
      have hab2 : b = a ∨ b = a + 1 := by omega
      rw [← hab]
      have : 2 * (a ^ 3 + b ^ 3) ≤ (a + b) ^ 3 := by
        have ha1 : 1 ≤ a := by omega
        rcases hab2 with rfl | rfl
        · ring_nf; omega
        · nlinarith [Nat.pow_le_pow_left ha1 2, Nat.pow_le_pow_left ha1 3]
      calc 2 * (B * a ^ 3 + B * b ^ 3) = B * (2 * (a ^ 3 + b ^ 3)) := by ring
        _ ≤ B * (a + b) ^ 3 := Nat.mul_le_mul_left _ this

theorem one_add_pow_two_pow (m : ℕ) (y : R m) (e : ℕ) : (1 + y) ^ 2 ^ e = 1 + y ^ 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, pow_mul, ih, pow_mul]
    have h2 := two_eq_zero m
    linear_combination (y ^ 2 ^ e) * h2

/-- All elementary matrices with entry 1. -/
theorem WL.el_one (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) :
    WL h2 (El i j hij 1 : G h n) (4 ^ (h + 3) * (2 * (n + 1)) ^ 3) := by
  obtain ⟨e, he1, he2⟩ : ∃ e, n + 1 ≤ 2 ^ e ∧ 2 ^ e ≤ 2 * (n + 1) := by
    refine ⟨Nat.clog 2 (n + 1), Nat.le_pow_clog (by omega) _, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := Nat.pow_pred_clog_lt_self (b := 2) (by omega) (show 1 < n + 1 by omega)
      have hc : 0 < Nat.clog 2 (n + 1) := Nat.clog_pos (by omega) (by omega)
      obtain ⟨c, hc'⟩ := Nat.exists_eq_add_of_lt hc
      rw [hc'] at this ⊢
      simp only [zero_add, Nat.pred_succ] at this ⊢
      rw [pow_succ]
      omega
  have h1 : t (n + 1) ^ 2 ^ e = 1 := by
    rw [t, one_add_pow_two_pow, s_pow_ge he1, add_zero]
  have h4 := WL.el_pow (n := n) (h2 := h2) h3 (fun i j hij => WL.el_t h3 i j hij) (2 ^ e)
    (Nat.one_le_pow _ _ (by omega)) i j hij
  rw [h1] at h4
  exact h4.mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he2 3))

/-- All elementary matrices with entry s. -/
theorem WL.el_s (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) :
    WL h2 (El i j hij (s (n + 1)) : G h n) (4 ^ (h + 3) * (9 * (n + 1) ^ 3)) := by
  have h1 := (WL.el_one (n := n) (h2 := h2) h3 i j hij).mul (WL.el_t h3 i j hij)
  rw [El_add, ← s_eq] at h1
  refine h1.mono ?_
  have : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  calc 4 ^ (h + 3) * (2 * (n + 1)) ^ 3 + 4 ^ (h + 3) = 4 ^ (h + 3) * (8 * (n + 1) ^ 3 + 1) := by ring
    _ ≤ 4 ^ (h + 3) * (9 * (n + 1) ^ 3) := Nat.mul_le_mul_left _ (by omega)

end Nc.Tower

end
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The diameter
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Matrix Finset

variable {h n : ℕ} [NeZero h] {h2 : 2 ≤ h}

/-- A trace-zero matrix whose layer element is a product of at most N generators. -/
def PL (h2 : 2 ≤ h) (n : ℕ) (A : Matrix (Fin h) (Fin h) (ZMod 2)) (N : ℕ) : Prop :=
  ∃ hA : A.trace = 0, WL h2 (lay (n := n) A hA) N

theorem lay_zero : lay (h := h) (n := n) 0 (trace_zero _ _) = 1 := by
  refine Subtype.ext ?_
  rw [lay_val, layMat]
  ext a b
  simp

theorem PL.zero (N : ℕ) : PL h2 n 0 N := ⟨trace_zero _ _, by rw [lay_zero]; exact WL.one.mono (Nat.zero_le _)⟩

theorem PL.add {A B : Matrix (Fin h) (Fin h) (ZMod 2)} {N M : ℕ} (hA : PL h2 n A N) (hB : PL h2 n B M) :
    PL h2 n (A + B) (N + M) := by
  obtain ⟨a1, a2⟩ := hA
  obtain ⟨b1, b2⟩ := hB
  exact ⟨by rw [trace_add, a1, b1, add_zero], by rw [← lay_mul A B a1 b1]; exact a2.mul b2⟩

theorem PL.sum {ι : Type*} (S : Finset ι) (M : ι → Matrix (Fin h) (Fin h) (ZMod 2)) (N : ℕ)
    (hM : ∀ p ∈ S, PL h2 n (M p) N) : PL h2 n (∑ p ∈ S, M p) (S.card * N) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using PL.zero (h2 := h2) (n := n) 0
  | insert p S hp ih =>
    rw [Finset.sum_insert hp, Finset.card_insert_of_notMem hp]
    have h1 := (hM p (mem_insert_self _ _)).add (ih fun q hq => hM q (mem_insert_of_mem hq))
    rwa [show (S.card + 1) * N = N + S.card * N by ring]

/-- The bound for one elementary matrix of the layer. -/
def bQ (h n : ℕ) : ℕ := 4 ^ (h + 3) * (9 * (n + 2) ^ 3) * (n + 1) ^ 3

theorem WL.el_layer (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) :
    WL h2 (El i j hij (s (n + 2) ^ (n + 1)) : G h (n + 1)) (bQ h n) :=
  WL.el_pow h3 (fun i j hij => WL.el_s h3 i j hij) (n + 1) (by omega) i j hij

theorem lay_single (i j : Fin h) (hij : i ≠ j) (htr : (Matrix.single i j (1 : ZMod 2)).trace = 0) :
    lay (n := n) (Matrix.single i j 1) htr = El i j hij (s (n + 2) ^ (n + 1)) := by
  refine Subtype.ext ?_
  rw [lay_val, layMat, El_val, transvection]
  congr 1
  ext a b
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs
  · rw [map_one, mul_one]
  · rw [map_zero, mul_zero]

theorem trace_single_ne (i j : Fin h) (hij : i ≠ j) : (Matrix.single i j (1 : ZMod 2)).trace = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Matrix.diag_apply, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hij rfl

theorem PL.single (h3 : 3 ≤ h) (i j : Fin h) (hij : i ≠ j) : PL h2 n (Matrix.single i j 1) (bQ h n) :=
  ⟨trace_single_ne i j hij, by rw [lay_single i j hij]; exact WL.el_layer h3 i j hij⟩

theorem trace_diag (i : Fin h) : (Matrix.single i i (1 : ZMod 2) + Matrix.single 0 0 1).trace = 0 := by
  rw [trace_add, Matrix.trace_single_eq_same, Matrix.trace_single_eq_same]
  rfl

/-- The diagonal elements of the layer. -/
theorem lay_diag (i : Fin h) (hi : i ≠ 0) :
    lay (n := n) (Matrix.single i i 1 + Matrix.single 0 0 1) (trace_diag i) =
      El 0 i hi.symm (s (n + 2) ^ (n + 1)) * El i 0 hi 1 *
        (El 0 i hi.symm (s (n + 2) ^ (n + 1)) * El i 0 hi 1) * El i 0 hi (s (n + 2) ^ (n + 1)) := by
  refine Subtype.ext ?_
  have hs : s (n + 2) ^ (n + 1) * s (n + 2) ^ (n + 1) = 0 := by rw [← sq, s_sq]
  set σ := s (n + 2) ^ (n + 1) with hσ
  simp only [Matrix.SpecialLinearGroup.coe_mul, El_val, transvection]
  have hl : layMat n (Matrix.single i i 1 + Matrix.single 0 0 1) =
      1 + (Matrix.single i i σ + Matrix.single 0 0 σ) := by
    rw [layMat, ← hσ]
    congr 1
    ext a b
    rw [Matrix.smul_apply, Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, Matrix.single_apply,
      Matrix.single_apply, Matrix.single_apply, Matrix.single_apply, smul_eq_mul, map_add, mul_add]
    congr 1
    · split_ifs
      · rw [map_one, mul_one]
      · rw [map_zero, mul_zero]
    · split_ifs
      · rw [map_one, mul_one]
      · rw [map_zero, mul_zero]
  rw [lay_val, hl]
  set a := Matrix.single (0 : Fin h) i σ with ha
  set b := Matrix.single i (0 : Fin h) (1 : R (n + 2)) with hb
  set c := Matrix.single i (0 : Fin h) σ with hc
  have haa : a * a = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hi _
  have hbb : b * b = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hi.symm _
  have hab : a * b = Matrix.single 0 0 σ := by rw [ha, hb, Matrix.single_mul_single_same, mul_one]
  have hba : b * a = Matrix.single i i σ := by rw [ha, hb, Matrix.single_mul_single_same, one_mul]
  have hbab : b * a * b = c := by rw [hba, hb, hc, Matrix.single_mul_single_same, mul_one]
  have haba : a * b * a = 0 := by rw [hab, ha, Matrix.single_mul_single_same, hs, Matrix.single_zero]
  have hac : a * c = 0 := by rw [ha, hc, Matrix.single_mul_single_same, hs, Matrix.single_zero]
  have hbc : b * c = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hi.symm _
  have hcc : c * c = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hi.symm _
  rw [← hab, ← hba]
  have e2 : (1 + a) * (1 + b) * ((1 + a) * (1 + b)) = 1 + (b * a + c + a * b) := by
    have e3 : (1 + a) * (1 + b) * ((1 + a) * (1 + b)) = 1 + ((a + b + a * b) + (a + b + a * b)) + (b * a + b * a * b +
      a * b) + (a * a + a * a * b + b * b + a * b * a + a * b * a * b + a * (b * b)) := by
      noncomm_ring
    rw [e3, two_nsmul_mat, haa, hbb, haba, hbab]
    simp
  have e4 : (1 + (b * a + c + a * b)) * (1 + c) = 1 + (b * a + a * b) + (c + c) +
      (b * (a * c) + c * c + a * (b * c)) := by noncomm_ring
  rw [e2, e4, two_nsmul_mat, hac, hcc, hbc]
  simp

theorem PL.diag (h3 : 3 ≤ h) (i : Fin h) : PL h2 n (Matrix.single i i 1 + Matrix.single 0 0 1) (5 * bQ h n) := by
  by_cases hi : i = 0
  · subst hi
    have : (Matrix.single 0 0 1 + Matrix.single 0 0 1 : Matrix (Fin h) (Fin h) (ZMod 2)) = 0 := by
      rw [← Matrix.single_add]
      exact Matrix.single_zero _ _
    rw [this]
    exact PL.zero _
  · refine ⟨trace_diag i, ?_⟩
    rw [lay_diag i hi]
    have p1 := WL.el_layer (n := n) (h2 := h2) h3 0 i (Ne.symm hi)
    have p2 := WL.el_one (n := n + 1) (h2 := h2) h3 i 0 hi
    have p3 := WL.el_layer (n := n) (h2 := h2) h3 i 0 hi
    refine (((p1.mul p2).mul (p1.mul p2)).mul p3).mono ?_
    have h4 : 4 ^ (h + 3) * (2 * (n + 1 + 1)) ^ 3 ≤ bQ h n := by
      unfold bQ
      have : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
      calc 4 ^ (h + 3) * (2 * (n + 1 + 1)) ^ 3 = 4 ^ (h + 3) * (8 * (n + 2) ^ 3) * 1 := by ring
        _ ≤ 4 ^ (h + 3) * (9 * (n + 2) ^ 3) * (n + 1) ^ 3 := by gcongr; omega
    omega

/-- The layer: a matrix as a sum of elementary ones. -/
theorem sum_layer (A : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) :
    ∑ p : Fin h × Fin h, A p.1 p.2 • (if p.1 = p.2 then Matrix.single p.1 p.1 1 + Matrix.single 0 0 1
      else Matrix.single p.1 p.2 1 : Matrix (Fin h) (Fin h) (ZMod 2)) = A := by
  ext a b
  rw [Matrix.sum_apply]
  have h1 : ∀ p : Fin h × Fin h, (A p.1 p.2 • (if p.1 = p.2 then Matrix.single p.1 p.1 1 + Matrix.single 0 0 1
      else Matrix.single p.1 p.2 1 : Matrix (Fin h) (Fin h) (ZMod 2))) a b =
      (if p = (a, b) then A p.1 p.2 else 0) + (if p.1 = p.2 then (if 0 = a ∧ 0 = b then A p.1 p.2 else 0) else 0) := by
    rintro ⟨i, j⟩
    simp only [Matrix.smul_apply, smul_eq_mul, Prod.mk.injEq]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, mul_add]
      congr 1
      · split_ifs <;> simp
      · split_ifs <;> simp
    · rw [if_neg hij, if_neg hij, Matrix.single_apply, add_zero]
      split_ifs <;> simp
  rw [Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_add_distrib, Finset.sum_ite_eq' univ (a, b), if_pos (mem_univ _)]
  have h3 : (∑ p : Fin h × Fin h, if p.1 = p.2 then (if 0 = a ∧ 0 = b then A p.1 p.2 else 0) else 0) = 0 := by
    rw [Fintype.sum_prod_type]
    by_cases hab : 0 = a ∧ 0 = b
    · obtain ⟨rfl, rfl⟩ := hab
      simp only [and_self, if_true, Finset.sum_ite_eq, mem_univ]
      exact hA
    · simp [hab]
  rw [h3, add_zero]

theorem PL.all (h3 : 3 ≤ h) (A : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) :
    PL h2 n A (h * h * (5 * bQ h n)) := by
  have h4 := PL.sum (h2 := h2) (n := n) (univ : Finset (Fin h × Fin h)) (fun p => A p.1 p.2 •
    (if p.1 = p.2 then Matrix.single p.1 p.1 1 + Matrix.single 0 0 1 else Matrix.single p.1 p.2 1)) (5 * bQ h n) (by
    rintro ⟨i, j⟩ -
    simp only
    have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases key (A i j) with h0 | h1
    · rw [h0, zero_smul]
      exact PL.zero _
    · rw [h1, one_smul]
      split_ifs with hij
      · exact PL.diag h3 i
      · obtain ⟨a1, a2⟩ := PL.single (h2 := h2) (n := n) h3 i j hij
        exact ⟨a1, a2.mono (by omega)⟩)
  rw [sum_layer A hA] at h4
  simpa using h4

theorem red_tt (k : Fin h) : red (n + 1) (tt (n + 1) k) = tt n k := by
  rw [tt, tt]
  split_ifs
  · exact red_t _
  · exact map_one _

theorem redG_gen (k : Fin h) : redG (gen h2 k : G h (n + 1)) = gen h2 k := by
  refine Subtype.ext ?_
  ext a b
  rw [redG_apply, gen_val, gen_val, transvection, transvection, Matrix.add_apply, Matrix.add_apply, map_add,
    Matrix.single_apply, Matrix.single_apply]
  congr 1
  · by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, map_zero]
  · split_ifs
    · exact red_tt k
    · exact map_zero _

/-- From level n to level n + 1. -/
theorem WL.lift (h3 : 3 ≤ h) {N : ℕ} (hN : ∀ g : G h n, WL h2 g N) (g : G h (n + 1)) :
    WL h2 g (N + h * h * (5 * bQ h n)) := by
  obtain ⟨l, h1, h4⟩ := hN (redG g)
  have h5 : redG ((l.map (Nc.Tower.gen h2)).prod : G h (n + 1)) = redG g := by
    rw [map_list_prod, List.map_map, ← h4]
    congr 1
    exact List.map_congr_left fun k _ => redG_gen k
  have h6 : redG (((l.map (Nc.Tower.gen h2)).prod : G h (n + 1))⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, h5, inv_mul_cancel]
  obtain ⟨A, hA, h7⟩ := exists_lay h6
  obtain ⟨hA', h8⟩ := PL.all (h2 := h2) (n := n) h3 A hA
  have h9 : g = (l.map (Nc.Tower.gen h2)).prod * lay A hA := by rw [← h7, mul_inv_cancel_left]
  rw [h9]
  exact (show WL h2 ((l.map (Nc.Tower.gen h2)).prod : G h (n + 1)) N from ⟨l, h1, rfl⟩).mul h8

end Nc.Tower

end
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The diameter of the first group; the diameter in general
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Matrix Finset

variable {h n : ℕ} [NeZero h] {h2 : 2 ≤ h}

/-- A transvection as an element of the group. -/
def tSL (τ : TransvectionStruct (Fin h) (ZMod 2)) : SL2 h := ⟨τ.toMatrix, τ.det⟩

theorem tSL_prod (l : List (TransvectionStruct (Fin h) (ZMod 2))) :
    ((l.map tSL).prod : SL2 h).1 = (l.map TransvectionStruct.toMatrix).prod := by
  induction l with
  | nil => rfl
  | cons τ l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    rfl

theorem exists_transvections (A : SL2 h) : ∃ l : List (TransvectionStruct (Fin h) (ZMod 2)), A = (l.map tSL).prod := by
  obtain ⟨L, L', D, hD⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A.1
  have h1 : ∏ i, D i = 1 := by
    have h3 := A.2
    rw [hD, det_mul, det_mul, TransvectionStruct.det_toMatrix_prod, TransvectionStruct.det_toMatrix_prod,
      det_diagonal, one_mul, mul_one] at h3
    exact h3
  have h3 : ∀ i, D i = 1 := by
    intro i
    have h4 : D i ≠ 0 := by
      intro h0
      rw [Finset.prod_eq_zero (mem_univ i) h0] at h1
      exact absurd h1 (by decide)
    have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    exact key _ h4
  have h5 : diagonal D = 1 := by
    have : D = fun _ => 1 := funext h3
    rw [this, diagonal_one]
  rw [h5, mul_one] at hD
  refine ⟨L ++ L', Subtype.ext ?_⟩
  rw [tSL_prod, List.map_append, List.prod_append]
  exact hD

theorem th0_tSL (τ : TransvectionStruct (Fin h) (ZMod 2)) : (th0 0 (tSL τ) : G h n) = El τ.i τ.j τ.hij (cst (n + 1) τ.c) := by
  refine Subtype.ext ?_
  ext a b
  have hw : ∀ a : Fin h, (wt 0 a : (R (n + 1))ˣ) = 1 := fun a => if_neg (Fin.not_lt_zero a)
  rw [th0_val, shMat_apply, hw, hw, sub_zero, sub_zero, El_val]
  have e : (tSL τ).1 = transvection τ.i τ.j τ.c := rfl
  rw [e, transvection, transvection, Matrix.add_apply, Matrix.add_apply, map_add, Matrix.single_apply,
    Matrix.single_apply]
  simp only [Units.val_one, inv_one, one_mul, mul_one]
  congr 1
  · by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, map_zero]
  · split_ifs
    · rfl
    · exact map_zero _

theorem WL.tSL (h3 : 3 ≤ h) (τ : TransvectionStruct (Fin h) (ZMod 2)) : ∃ N, WL h2 (th0 0 (tSL τ) : G h n) N := by
  rw [th0_tSL]
  have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases key τ.c with h0 | h1
  · refine ⟨0, ?_⟩
    have : (El τ.i τ.j τ.hij (cst (n + 1) τ.c) : G h n) = 1 := by
      refine Subtype.ext ?_
      rw [El_val, h0, map_zero, transvection_zero]
      rfl
    rw [this]
    exact WL.one
  · refine ⟨4 ^ (h + 3) * (2 * (n + 1)) ^ 3, ?_⟩
    rw [h1, map_one]
    exact WL.el_one h3 τ.i τ.j τ.hij

theorem WL.const (h3 : 3 ≤ h) (A : SL2 h) : ∃ N, WL h2 (th0 0 A : G h n) N := by
  obtain ⟨l, rfl⟩ := exists_transvections A
  induction l with
  | nil => exact ⟨0, by simpa using WL.one⟩
  | cons τ l ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := WL.tSL (n := n) (h2 := h2) h3 τ
    refine ⟨M + N, ?_⟩
    rw [List.map_cons, List.prod_cons, map_mul]
    exact hM.mul hN

theorem exists_base (h2 : 2 ≤ h) (h3 : 3 ≤ h) : ∃ C, ∀ g : G h 0, WL h2 g C := by
  have h1 : ∀ g : G h 0, ∃ N, WL h2 g N := by
    intro g
    obtain ⟨N, hN⟩ := WL.const (n := 0) (h2 := h2) h3 (evG g)
    refine ⟨N, ?_⟩
    have : g = th0 0 (evG g) := by
      apply evG_bijective_zero.1
      refine Subtype.ext ?_
      ext a b
      rw [evG_th0, sub_zero, sub_zero]
    rw [this]
    exact hN
  choose N hN using h1
  exact ⟨univ.sup N, fun g => (hN g).mono (Finset.le_sup (mem_univ g))⟩

/-- **The diameter.** -/
theorem exists_diam (h : ℕ) [NeZero h] (h2 : 2 ≤ h) (h3 : 3 ≤ h) :
    ∃ C, ∀ (n : ℕ) (g : G h n), WL h2 g (C * (n + 1) ^ 7) := by
  obtain ⟨C, hC⟩ := exists_base h2 h3
  let B := h * h * (5 * (4 ^ (h + 3) * 9 * 8))
  refine ⟨C + B, fun n => ?_⟩
  induction n with
  | zero => intro g; exact (hC g).mono (by simp)
  | succ n ih =>
    intro g
    refine (WL.lift h3 ih g).mono ?_
    have h4 : h * h * (5 * bQ h n) ≤ B * (n + 1) ^ 6 := by
      have h5 : (n + 2) ^ 3 ≤ 8 * (n + 1) ^ 3 := by
        calc (n + 2) ^ 3 ≤ (2 * (n + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
          _ = 8 * (n + 1) ^ 3 := by ring
      have h6 : bQ h n ≤ 4 ^ (h + 3) * 9 * 8 * (n + 1) ^ 6 := by
        unfold bQ
        calc 4 ^ (h + 3) * (9 * (n + 2) ^ 3) * (n + 1) ^ 3 ≤ 4 ^ (h + 3) * (9 * (8 * (n + 1) ^ 3)) * (n + 1) ^ 3 := by
              gcongr
          _ = _ := by ring
      calc h * h * (5 * bQ h n) ≤ h * h * (5 * (4 ^ (h + 3) * 9 * 8 * (n + 1) ^ 6)) := by gcongr
        _ = B * (n + 1) ^ 6 := by simp only [B]; ring
    have h7 : (n + 1) ^ 7 + (n + 1) ^ 6 ≤ (n + 1 + 1) ^ 7 := by
      have h8 : (n + 1) ^ 6 ≤ (n + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      calc (n + 1) ^ 7 + (n + 1) ^ 6 = (n + 1) ^ 6 * (n + 2) := by ring
        _ ≤ (n + 2) ^ 6 * (n + 2) := Nat.mul_le_mul_right _ h8
        _ = (n + 1 + 1) ^ 7 := by ring
    calc (C + B) * (n + 1) ^ 7 + h * h * (5 * bQ h n) ≤ (C + B) * (n + 1) ^ 7 + B * (n + 1) ^ 6 :=
          Nat.add_le_add_left h4 _
      _ ≤ (C + B) * (n + 1) ^ 7 + (C + B) * (n + 1) ^ 6 := by
          refine Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
      _ = (C + B) * ((n + 1) ^ 7 + (n + 1) ^ 6) := by ring
      _ ≤ (C + B) * (n + 1 + 1) ^ 7 := Nat.mul_le_mul_left _ h7

end Nc.Tower

end
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The tower as a structure, and routes
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Finset

attribute [-instance] Subtype.instBEq



variable (h n : ℕ) [NeZero h]

/-- **The tower.** -/
noncomputable def tower (h2 : 2 ≤ h) : Nc.Tow.Tower h (2 ^ ee h) (2 ^ ee h) (JJ h n) 1 where
  X := XX h n
  Ed := EE h n h2
  V := VV h n
  Fl := U h
  Nr := NN h
  fX := instFintypeXX h n
  dX := instDecXX h n
  fE := instFintypeEE h2
  dE := instDecEE h2
  fV := instFintypeVV
  dV := instDecVV
  fF := inferInstance
  dF := inferInstance
  fN := inferInstance
  dN' := inferInstance
  e0 := fun e => e.1.2
  e1 := fun e => (gen h2 e.1.1 : G h n) • e.1.2
  e_ne := fun e => (gen_smul_ne h2 _ _).symm
  ty := fun e => e.1.1
  card_ed := fun j _ i => card_edges h2 j i
  deg := fun j _ c i => deg_edges h2 j c i
  vx := vert
  co := cor
  vx_co := fun _ i => vert_cor_bijective _ i
  card_fl := card_U h
  cN := fun ν => ν.1.2
  dN := fun ν => x h ν.1.1 * ν.1.2
  n_ne := fun ν e => x_ne_one ν.1.1 (by simpa using e.symm)
  nr := fun _ i => Equiv.ofBijective _ (nearFun_bijective h2 _ i)
  nr_vx0 := fun _ i e => rfl
  nr_vx1 := fun _ i e => by
    change vert i ((gen h2 e.1.1.1 : G h n) • e.1.1.2) = vert i e.1.1.2
    rw [gen_idx h2 i _ e.2, vert_th]
  nr_co := fun _ i e => by
    change s(cor i e.1.1.2, cor i ((gen h2 e.1.1.1 : G h n) • e.1.1.2)) =
      s((npair (idx i e.1.1.1 e.2) (cor i e.1.1.2)).1.2,
        x h (npair (idx i e.1.1.1 e.2) (cor i e.1.1.2)).1.1 * (npair (idx i e.1.1.1 e.2) (cor i e.1.1.2)).1.2)
    rw [gen_idx h2 i _ e.2, cor_th]
    exact npair_sym _ _
  π := pr
  πE := prE h2
  πV := prV
  π_ends := fun _ e => by
    change s(pr e.1.2, (gen h2 e.1.1 : G h n) • pr e.1.2) = s(pr e.1.2, pr ((gen h2 e.1.1 : G h n) • e.1.2))
    rw [Paper.prop_tower_equivariant]
  π_ty := fun _ _ => rfl
  card_X := fun _ hj => card_XX_succ hj
  fibre := fun hj d => fibre_edges h2 hj d
  π_vx := fun _ i c => vert_pr i c
  π_co := fun _ i c => cor_pr i c
  host := fun {j} i => (exists_host (n := n) j i).choose
  host_inj := fun {j} hj i => ((exists_host (n := n) j i).choose_spec hj).1
  host_vx := fun {j} hj i v => ((exists_host (n := n) j i).choose_spec hj).2 v

variable {h n}

/-- The edges along a list of types. -/
noncomputable def path (h2 : 2 ≤ h) {j : ℕ} : List (Fin h) → XX h n j → List (EE h n h2 j)
  | [], _ => []
  | k :: l, c => edge h2 k c :: path h2 l ((gen h2 k : G h n) • c)

theorem length_path (h2 : 2 ≤ h) {j : ℕ} (l : List (Fin h)) (c : XX h n j) : (path h2 l c).length = l.length := by
  induction l generalizing c with
  | nil => rfl
  | cons k l ih => rw [path, List.length_cons, ih, List.length_cons]

theorem step_edge (h2 : 2 ≤ h) {j : ℕ} (k : Fin h) (c : XX h n j) :
    (tower h n h2).step (edge h2 k c) c = (gen h2 k : G h n) • c := by
  have hu : (tower h n h2).step (edge h2 k c) c = if (edge h2 k c).1.2 = c then
      (gen h2 (edge h2 k c).1.1 : G h n) • (edge h2 k c).1.2 else (edge h2 k c).1.2 := rfl
  rw [hu, edge_type]
  rcases edge_end h2 k c with e | e
  · rw [if_pos e, e]
  · rw [if_neg, e]
    rw [e]
    exact gen_smul_ne h2 k c

theorem walk_path (h2 : 2 ≤ h) {j : ℕ} (l : List (Fin h)) (c : XX h n j) :
    (tower h n h2).Walk c (path h2 l c) (((l.reverse.map (gen h2)).prod : G h n) • c : XX h n j) := by
  induction l generalizing c with
  | nil =>
    change c = ((([] : List (Fin h)).reverse.map (gen h2)).prod : G h n) • c
    simp
  | cons k l ih =>
    refine ⟨?_, ?_⟩
    · rcases edge_end h2 k c with e | e
      · exact Or.inl e
      · right
        change (gen h2 (edge h2 k c).1.1 : G h n) • (edge h2 k c).1.2 = c
        rw [edge_type, e, gen_gen]
    · rw [step_edge]
      have h3 := ih ((gen h2 k : G h n) • c)
      rw [← mul_smul] at h3
      simpa using h3

theorem count_path (h2 : 2 ≤ h) {j : ℕ} (l : List (Fin h)) (e : EE h n h2 j) :
    ∑ c : XX h n j, (path h2 l c).count e ≤ 2 * l.length := by
  induction l with
  | nil => simp [path]
  | cons k l ih =>
    have h1 : ∀ c : XX h n j, (path h2 (k :: l) c).count e =
        (path h2 l ((gen h2 k : G h n) • c)).count e + if edge h2 k c = e then 1 else 0 := by
      intro c
      rw [path, List.count_cons]
      simp only [beq_iff_eq]
    rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_add_distrib]
    have h3 : ∑ c : XX h n j, (path h2 l ((gen h2 k : G h n) • c)).count e = ∑ c : XX h n j, (path h2 l c).count e :=
      Equiv.sum_comp (MulAction.toPerm (gen h2 k : G h n)) fun c => (path h2 l c).count e
    have h4 : (∑ c : XX h n j, if edge h2 k c = e then 1 else 0) ≤ 2 := by
      rw [← Finset.card_filter]
      have h5 : (univ.filter fun c : XX h n j => edge h2 k c = e) ⊆ {e.1.2, (gen h2 k : G h n) • e.1.2} := by
        intro c hc
        rw [mem_filter] at hc
        rw [mem_insert, mem_singleton]
        rcases edge_end h2 k c with e1 | e1
        · left
          rw [← hc.2, e1]
        · right
          rw [← hc.2, e1, gen_gen]
      exact (Finset.card_le_card h5).trans Finset.card_le_two
    rw [h3, List.length_cons]
    omega

/-- The chambers of the first level are the elements of the group. -/
theorem smul_bijective (c : XX h n 0) : Function.Bijective fun g : G h n => g • c := by
  constructor
  · intro g g' e
    induction c using QuotientGroup.induction_on with
    | H a =>
      have e1 : (QuotientGroup.mk (g * a) : XX h n 0) = QuotientGroup.mk (g' * a) := e
      have e2 := QuotientGroup.eq.1 e1
      rw [Gam_zero, Subgroup.mem_bot] at e2
      have e3 : g * a = g' * a := inv_mul_eq_one.1 e2
      exact mul_right_cancel e3
  · intro d
    exact MulAction.exists_smul_eq (G h n) c d

/-- The route. -/
noncomputable def rte (h2 : 2 ≤ h) (w : G h n → List (Fin h)) (c c' : XX h n 0) : List (EE h n h2 0) :=
  path h2 (w ((Equiv.ofBijective _ (smul_bijective c)).symm c')).reverse c

theorem rte_walk (h2 : 2 ≤ h) (w : G h n → List (Fin h)) (hw : ∀ g, ((w g).map (gen h2)).prod = g) (c c' : XX h n 0) :
    (tower h n h2).Walk c (rte h2 w c c') c' := by
  have h1 := walk_path h2 (w ((Equiv.ofBijective _ (smul_bijective c)).symm c')).reverse c
  rw [List.reverse_reverse, hw] at h1
  have h3 : ((Equiv.ofBijective _ (smul_bijective c)).symm c' : G h n) • c = c' :=
    (Equiv.ofBijective _ (smul_bijective c)).apply_symm_apply c'
  rw [h3] at h1
  exact h1

theorem rte_length (h2 : 2 ≤ h) (w : G h n → List (Fin h)) {m : ℕ} (hw : ∀ g, (w g).length ≤ m) (c c' : XX h n 0) :
    (rte h2 w c c').length ≤ m := by
  rw [rte, length_path, List.length_reverse]
  exact hw _

theorem rte_use (h2 : 2 ≤ h) (w : G h n → List (Fin h)) {m : ℕ} (hw : ∀ g, (w g).length ≤ m) (e : EE h n h2 0) :
    ∑ c, ∑ c', (rte h2 w c c').count e ≤ 2 * (Fintype.card (XX h n 0) * m) := by
  classical
  have h1 : ∀ c : XX h n 0, ∑ c' : XX h n 0, (rte h2 w c c').count e =
      ∑ g : G h n, (path h2 (w g).reverse c).count e := fun c =>
    Equiv.sum_comp (Equiv.ofBijective _ (smul_bijective c)).symm fun g => (path h2 (w g).reverse c).count e
  rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_comm]
  calc ∑ g : G h n, ∑ c : XX h n 0, (path h2 (w g).reverse c).count e ≤ ∑ _g : G h n, 2 * m := by
        refine Finset.sum_le_sum fun g _ => (count_path h2 _ e).trans ?_
        rw [List.length_reverse]
        exact Nat.mul_le_mul_left _ (hw g)
    _ = 2 * (Fintype.card (XX h n 0) * m) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Fintype.card_congr (Equiv.ofBijective _ (smul_bijective (QuotientGroup.mk 1 : XX h n 0)))]
        ring

/-- **Routes.** -/
theorem exists_routes (h2 : 2 ≤ h) {m : ℕ} (hm : ∀ g : G h n, WL h2 g m) :
    Nonempty (Nc.Tow.Routes (tower h n h2) m (2 * (Fintype.card (XX h n 0) * m))) := by
  choose w hw1 hw2 using hm
  exact ⟨{ rt := rte h2 w
           walk := rte_walk h2 w hw2
           len := rte_length h2 w hw1
           use := rte_use h2 w hw1 }⟩

/-- Sums over the near pairs. -/
theorem sum_NN {M : Type*} [AddCommMonoid M] (f : Fin (h - 1) → U h → M) (hf : ∀ l u, f l (x h l * u) = f l u) :
    ∑ l, ∑ u, f l u = ∑ ν : NN h, f ν.1.1 ν.1.2 + ∑ ν : NN h, f ν.1.1 ν.1.2 := by
  classical
  rw [← Fintype.sum_prod_type (fun p : Fin (h - 1) × U h => f p.1 p.2),
    ← Finset.sum_filter_add_sum_filter_not univ (fun p : Fin (h - 1) × U h => FU p.1 p.2)]
  have h1 : ∑ p ∈ univ.filter (fun p : Fin (h - 1) × U h => FU p.1 p.2), f p.1 p.2 = ∑ ν : NN h, f ν.1.1 ν.1.2 := by
    refine Finset.sum_bij' (fun p hp => (⟨p, (mem_filter.1 hp).2⟩ : NN h)) (fun ν _ => ν.1) ?_ ?_ ?_ ?_ ?_
    · intro p _; exact mem_univ _
    · intro ν _; exact mem_filter.2 ⟨mem_univ _, ν.2⟩
    · intro p _; rfl
    · intro ν _; rfl
    · intro p _; rfl
  have h3 : ∑ p ∈ univ.filter (fun p : Fin (h - 1) × U h => ¬ FU p.1 p.2), f p.1 p.2 =
      ∑ p ∈ univ.filter (fun p : Fin (h - 1) × U h => FU p.1 p.2), f p.1 p.2 := by
    refine Finset.sum_bij' (fun p _ => (p.1, x h p.1 * p.2)) (fun p _ => (p.1, x h p.1 * p.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_filter] at hp ⊢
      exact ⟨mem_univ _, (FU_iff _ _).2 hp.2⟩
    · intro p hp
      rw [mem_filter] at hp ⊢
      exact ⟨mem_univ _, fun e => (FU_iff _ _).1 e hp.2⟩
    · intro p _
      refine Prod.ext rfl ?_
      change x h p.1 * (x h p.1 * p.2) = p.2
      rw [← mul_assoc, x_mul_self, one_mul]
    · intro p _
      refine Prod.ext rfl ?_
      change x h p.1 * (x h p.1 * p.2) = p.2
      rw [← mul_assoc, x_mul_self, one_mul]
    · intro p _
      exact (hf _ _).symm
  rw [h3, h1]

section Numbers

variable (h n)

theorem card_XJ (h2 : 2 ≤ h) :
    Fintype.card ((tower h n h2).X (JJ h n)) < Nat.card (SL2 h) * 2 ^ ee h := by
  have h1 := card_XX (h := h) (n := n) (j := JJ h n) le_rfl
  rw [card_G] at h1
  have he : 0 < ee h := by
    unfold ee
    have : 2 ≤ h * (h - 1) := by
      calc 2 = 2 * 1 := rfl
        _ ≤ h * (h - 1) := Nat.mul_le_mul h2 (by omega)
    omega
  have h3 : (h ^ 2 - 1) * n < ee h * (JJ h n + 1) := by
    have := Nat.lt_mul_div_succ ((h ^ 2 - 1) * n) he
    unfold JJ
    omega
  have h4 : 2 ^ ((h ^ 2 - 1) * n) < (2 ^ ee h) ^ (JJ h n) * 2 ^ ee h := by
    rw [← pow_succ, ← pow_mul]
    exact Nat.pow_lt_pow_right (by omega) h3
  have hp : 0 < (2 ^ ee h) ^ JJ h n := Nat.pow_pos (Nat.pow_pos (by omega))
  refine Nat.lt_of_mul_lt_mul_right (a := (2 ^ ee h) ^ JJ h n) ?_
  have h5 : Fintype.card ((tower h n h2).X (JJ h n)) * (2 ^ ee h) ^ JJ h n = Nat.card (SL2 h) * 2 ^ ((h ^ 2 - 1) * n) := h1
  rw [h5, mul_assoc, mul_comm (2 ^ ee h)]
  exact Nat.mul_lt_mul_of_pos_left h4 Nat.card_pos

end Numbers

end Nc.Tower

end
namespace Nc.Tow
open Finset Nc.G
/-- The laws at the vertices of a tower with the given local structure. -/
def VLaws.toFlag {F : Type} [CommRing F] {Fl Nr : Type} [Fintype Fl] [DecidableEq Fl] [Fintype Nr]
    [DecidableEq Nr] {cN dN : Nr → Fl} {r b : ℕ} (VL : VLaws F cN dN r b) {h D J : ℕ}
    (T : Tower h b D J r) (φ : T.Fl ≃ Fl) (ψ : T.Nr ≃ Nr)
    (hφ : ∀ ν, s(φ (T.cN ν), φ (T.dN ν)) = s(cN (ψ ν), dN (ψ ν))) : FlagLaws F T where
  Di := VL.Di
  L := VL.L
  ro d := (VL.ro d).trans φ.symm
  cn d := (VL.cn d).trans ψ.symm
  ends d ν := by
    have h1 := hφ (ψ.symm (VL.cn d ν))
    rw [ψ.apply_symm_apply, ← VL.ends d ν] at h1
    have h2 := congrArg (Sym2.map φ.symm) h1
    simpa [Sym2.map_mk] using h2.symm
  lam_pos := VL.lam_pos
  nonempty := VL.nonempty
  a₁ := VL.a₁
  a₁_pos := VL.a₁_pos
  C₁ := VL.C₁
  C₁_nonneg := VL.C₁_nonneg
  G₁ := VL.G₁
  G₁_le := VL.G₁_le
  L1 n t ht := by
    have hN : vN2 b (fun q : Sym2 Fl => n (Sym2.map φ.symm q)) = T.NN2 n := by
      rw [vN2, Tower.NN2]
      congr 1
      let e : Sym2 Fl ≃ Sym2 T.Fl := ⟨Sym2.map φ.symm, Sym2.map φ,
        fun q => by rw [Sym2.map_map]; simp, fun q => by rw [Sym2.map_map]; simp⟩
      refine Fintype.sum_equiv e _ _ fun q => ?_
      have hd : (Sym2.map φ.symm q).IsDiag ↔ q.IsDiag :=
        Sym2.isDiag_map φ.symm.injective
      show (if q.IsDiag then 0 else _) = if (Sym2.map φ.symm q).IsDiag then 0 else _
      simp only [hd]
      rfl
    obtain ⟨d, hd⟩ := VL.L1 (fun q => n (Sym2.map φ.symm q)) t (by rw [hN]; exact ht)
    refine ⟨d, fun q hq => ?_⟩
    have h1 := hd (Sym2.map φ q) (fun h => hq ((Sym2.isDiag_map φ.injective).1 h))
    have h2 : Sym2.map φ.symm (Sym2.map φ q) = q := by
      rw [Sym2.map_map]
      simp
    rw [h2] at h1
    refine h1.trans (Nat.mul_le_mul_right _ (Finset.card_le_card fun e he => ?_))
    rw [Finset.mem_filter] at he ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h3 := congrArg (Sym2.map φ.symm) he.2
    rw [h2] at h3
    simpa [Sym2.map_mk] using h3
  L2 := VL.L2


end Nc.Tow
namespace Nc.Vp
open Nc.Tow Nc.Tower
/-- The laws at the vertices of the tower of U h with parameter n. -/
noncomputable def towFlag {F : Type} [CommRing F] {h : ℕ} [NeZero h]
    (VL : VLaws F (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h2 : 2 ≤ h) (n : ℕ) :
    FlagLaws F (tower h n h2) :=
  VL.toFlag (tower h n h2) (Equiv.refl (U h)) (Equiv.refl (NN h)) fun _ => rfl


end Nc.Vp
namespace Paper
open Finset Nc.Tow Nc.Vp
open Nc.Tower (U x NN ee JJ tower SL2 gen XX npair npair_sym)
def _root_.Nc.Tow.Routes.mono {h b D J r m Uu m' Uu' : ℕ} {T : Tower h b D J r} (R : Routes T m Uu) (hm : m ≤ m')
    (hU : Uu ≤ Uu') : Routes T m' Uu' where
  rt := R.rt
  walk := R.walk
  len c c' := (R.len c c').trans hm
  use e := (R.use e).trans hU

/-- "Take the least n ≥ 1 with M ≤ |G_n|; so |G_n| = O(M)": towers of all sizes from Proposition prop:tower, whose
parts (c) and (d) give the size, the bottom and the words of the routes. -/
theorem tree_towers {A : Type} [CommRing A] {h : ℕ} [NeZero h]
    (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (1 / 2 : ℝ) ^ 2 * h) (htwo : (2 : ℝ) ≤ 1 / 2 * ((2 ^ ee h : ℕ) : ℝ)) :
    ∃ c, ∀ y, 1 ≤ y → ∃ (J m Uu : ℕ) (T : Tower h (2 ^ ee h) (2 ^ ee h) J 1) (_ : Routes T m Uu) (FL : FlagLaws A T),
      FL.G₁ = VL.G₁ ∧ TCst FL ((univ : Finset VL.Di).toList.map VL.L) c (1 / 2) 1 (ee h) ∧
      y ≤ Fintype.card (T.X 0) ∧ Fintype.card (T.X 0) ≤ c * y ∧ 1 ≤ m ∧ m ≤ c * (J + 1) ^ 7 ∧
      Uu ≤ 2 * Fintype.card (T.X 0) * m := by
  classical
  have h2 : 2 ≤ h := by omega
  obtain ⟨C, hC⟩ := Nc.Tower.exists_diam h (by omega) h3
  have hee2 : 2 ≤ ee h := by
    unfold Nc.Tower.ee
    have : 3 * 2 ≤ h * (h - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  have heeh : ee h ≤ h ^ 2 - 1 := by
    unfold Nc.Tower.ee
    have h4 : h * (h - 1) ≤ h * h := Nat.mul_le_mul_left _ (by omega)
    have h5 : h ^ 2 = h * h := by ring
    have h6 : 9 ≤ h * h := Nat.mul_le_mul h3 h3
    omega
  let S : ℕ := Nat.card (SL2 h)
  let g : ℕ → ℕ := fun n => Nat.card (Nc.Tower.G h n)
  have hg0 : ∀ n, g (n + 1) = g n * 2 ^ (h ^ 2 - 1) := fun n => Nc.Tower.card_G_succ
  have hg1 : ∀ n, 0 < g n := fun n => Nat.card_pos
  have hS : 0 < S := Nat.card_pos
  obtain ⟨c, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩ : ∃ c : ℕ, h ≤ c ∧ 2 ^ ee h ≤ c ∧ 3 ≤ c ∧
      Fintype.card (NN h) ≤ c ∧ VL.G₁ ≤ c ∧ Fintype.card VL.Di ≤ c ∧ Fintype.card (Sym2 (U h)) ≤ c ∧
      ∑ d, Fintype.card (VL.L d).Sl ≤ c ∧ ∑ d, ∑ i, ∑ ν, (VL.L d).len i ν ≤ c ∧ ∑ d, (VL.L d).lam ≤ c ∧
      ⌈√(h : ℝ) * ((1 : ℕ) : ℝ) + √VL.C₁ * VL.a₁⌉₊ ≤ c ∧ S * 2 ^ ee h ≤ c ∧ g 0 ≤ c ∧ 2 ^ (h ^ 2 - 1) ≤ c ∧ C + 1 ≤ c := by
    let l : List ℕ := [h, 2 ^ ee h, 3, Fintype.card (NN h), VL.G₁, Fintype.card VL.Di, Fintype.card (Sym2 (U h)),
      ∑ d, Fintype.card (VL.L d).Sl, ∑ d, ∑ i, ∑ ν, (VL.L d).len i ν, ∑ d, (VL.L d).lam,
      ⌈√(h : ℝ) * ((1 : ℕ) : ℝ) + √VL.C₁ * VL.a₁⌉₊, S * 2 ^ ee h, g 0, 2 ^ (h ^ 2 - 1), C + 1]
    have hl : ∀ a ∈ l, a ≤ l.sum := fun a ha => List.single_le_sum (fun _ _ => Nat.zero_le _) a ha
    refine ⟨l.sum, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_,
      hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_⟩ <;> simp only [l, List.mem_cons, true_or, or_true]
  refine ⟨c, fun y hy => ?_⟩
  -- the least size
  have hg2 : ∀ n, 2 ^ n ≤ g n := by
    intro n
    induction n with
    | zero => exact hg1 0
    | succ n ih =>
      rw [hg0, pow_succ]
      exact Nat.mul_le_mul ih (Nat.le_self_pow (by omega) 2)
  have hex : ∃ n, y ≤ g n := ⟨y, (Nat.lt_two_pow_self).le.trans (hg2 y)⟩
  let n := Nat.find hex
  have hn1 : y ≤ g n := Nat.find_spec hex
  have hn2 : g n ≤ c * y := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]
      exact k13.trans (Nat.le_mul_of_pos_right _ hy)
    · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have h4 : ¬ y ≤ g k := Nat.find_min hex (by
        show k < n
        omega)
      rw [hk, hg0, mul_comm c y]
      exact Nat.mul_le_mul (by omega) k14
  have hnJ : n ≤ JJ h n := by
    unfold Nc.Tower.JJ
    rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
    exact Nat.mul_le_mul_right _ heeh
  have hG0 : Fintype.card (XX h n 0) = g n := by
    simpa [g, Nat.card_eq_fintype_card] using Nc.Tower.card_XX (h := h) (n := n) (j := 0) (Nat.zero_le _)
  have hXJ := Nc.Tower.card_XJ h n (by omega)
  have hword := hC n
  obtain ⟨R⟩ := Nc.Tower.exists_routes (h := h) (n := n) h2 hword
  have hX0 : Fintype.card ((tower h n h2).X 0) = g n := hG0
  have hX0' : Fintype.card (XX h n 0) = g n := hG0
  have hXJ0 : 0 < Fintype.card ((tower h n h2).X (JJ h n)) :=
    Fintype.card_pos_iff.2 ⟨((QuotientGroup.mk 1 : XX h n (JJ h n)))⟩
  refine ⟨JJ h n, (C + 1) * (n + 1) ^ 7, 2 * Fintype.card ((tower h n h2).X 0) * ((C + 1) * (n + 1) ^ 7),
    tower h n h2, R.mono (Nat.mul_le_mul_right _ (by omega)) ?_, towFlag VL h2 n, rfl, ?_, ?_, ?_, ?_, ?_, le_rfl⟩
  · rw [hX0, hX0', ← mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  · have hlaw : ∀ d : VL.Di, VL.L d ∈ (univ : Finset VL.Di).toList.map VL.L := fun d =>
      List.mem_map.2 ⟨d, Finset.mem_toList.2 (mem_univ d), rfl⟩
    refine ⟨⟨one_pos, by positivity, by omega, by omega, by norm_num, by norm_num, hgain, htwo, ?_⟩, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, hXJ0, ?_, ?_, ?_, ?_, hlaw, ?_⟩
    · intro (f : U h)
      have h4 := npair_sym (⟨0, by omega⟩ : Fin (h - 1)) f
      rcases Sym2.eq_iff.1 h4 with ⟨e1, -⟩ | ⟨e1, -⟩
      · exact ⟨npair ⟨0, by omega⟩ f, Or.inl e1.symm⟩
      · exact ⟨npair ⟨0, by omega⟩ f, Or.inr e1.symm⟩
    · exact k1
    · exact k2
    · omega
    · refine (Fintype.card_congr (Equiv.refl _)).le.trans (?_ : Fintype.card (NN h) ≤ c)
      exact k4
    · exact k5
    · refine (Fintype.card_congr (Equiv.refl _)).le.trans (?_ : Fintype.card VL.Di ≤ c)
      exact k6
    · refine (Fintype.card_congr (Equiv.refl _)).le.trans (?_ : Fintype.card (Sym2 (U h)) ≤ c)
      exact k7
    · intro d
      have h4 : Fintype.card (VL.L d).Sl ≤ ∑ d, Fintype.card (VL.L d).Sl :=
        Finset.single_le_sum (f := fun d => Fintype.card (VL.L d).Sl) (fun _ _ => Nat.zero_le _) (mem_univ d)
      exact h4.trans k8
    · exact hXJ.le.trans k12
    · show √(h : ℝ) * ((1 : ℕ) : ℝ) + √VL.C₁ * VL.a₁ ≤ (c : ℝ)
      exact (Nat.le_ceil _).trans (Nat.cast_le.2 k11)
    · have h4 : (1 : ℝ) / (1 - 1 / 2) = ((2 : ℕ) : ℝ) := by norm_num
      rw [h4]
      exact Nat.cast_le.2 (by omega)
    · omega
    · have h4 : (1 / 2 : ℝ) ^ ee h * (((2 ^ ee h : ℕ) : ℝ)) ^ 1 = 1 := by
        push_cast
        rw [pow_one, ← mul_pow]
        norm_num
      exact h4.le
    · intro L hL
      rw [List.mem_map] at hL
      obtain ⟨d, -, rfl⟩ := hL
      refine ⟨⟨fun i ν => ?_⟩, ?_⟩
      · have h4 : (VL.L d).len i ν ≤ ∑ ν, (VL.L d).len i ν :=
          Finset.single_le_sum (f := fun ν => (VL.L d).len i ν) (fun _ _ => Nat.zero_le _) (mem_univ ν)
        have h5 : ∑ ν, (VL.L d).len i ν ≤ ∑ i, ∑ ν, (VL.L d).len i ν :=
          Finset.single_le_sum (f := fun i => ∑ ν, (VL.L d).len i ν) (fun _ _ => Nat.zero_le _) (mem_univ i)
        have h6 : ∑ i, ∑ ν, (VL.L d).len i ν ≤ ∑ d, ∑ i, ∑ ν, (VL.L d).len i ν :=
          Finset.single_le_sum (f := fun d => ∑ i, ∑ ν, (VL.L d).len i ν) (fun _ _ => Nat.zero_le _) (mem_univ d)
        exact h4.trans (h5.trans (h6.trans k9))
      · have h4 : (VL.L d).lam ≤ ∑ d, (VL.L d).lam :=
          Finset.single_le_sum (f := fun d => (VL.L d).lam) (fun _ _ => Nat.zero_le _) (mem_univ d)
        exact h4.trans k10
  · rw [hX0]; exact hn1
  · rw [hX0]; exact hn2
  · exact Nat.mul_pos (by omega) (by positivity)
  · exact Nat.mul_le_mul k15 (Nat.pow_le_pow_left (by omega) 7)


end Paper
open Finset Nc.Tow Nc.Vp
open Nc.Tower (ee)
theorem solution {A : Type} [CommRing A] {h : ℕ} [NeZero h]
    (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (1 / 2 : ℝ) ^ 2 * h) (htwo : (2 : ℝ) ≤ 1 / 2 * ((2 ^ ee h : ℕ) : ℝ)) :
    ∃ c, ∀ y, 1 ≤ y → ∃ (J m Uu : ℕ) (T : Tower h (2 ^ ee h) (2 ^ ee h) J 1) (_ : Routes T m Uu) (FL : FlagLaws A T),
      FL.G₁ = VL.G₁ ∧ TCst FL ((univ : Finset VL.Di).toList.map VL.L) c (1 / 2) 1 (ee h) ∧
      y ≤ Fintype.card (T.X 0) ∧ Fintype.card (T.X 0) ≤ c * y ∧ 1 ≤ m ∧ m ≤ c * (J + 1) ^ 7 ∧
      Uu ≤ 2 * Fintype.card (T.X 0) * m := Paper.tree_towers VL h3 hgain htwo
