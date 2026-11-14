-- Prove2me | solution 1 for QAlgorithms.Nannicini.qaoa_approximates_adiabatic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T06:57:22.156552+00:00
-- url     : https://prove2.me/submissions/b37c8e3b-9695-4272-82d1-80706b8ec303

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Theorems.Thm_QAlgorithms_Nannicini_adiabatic_theorem_linInterp
set_option autoImplicit false


/-! C1 infrastructure for 52c231a1: generic spectral facts (Rayleigh bounds from the eigenbasis,
minimisers are eigenvectors) and the Perron-Frobenius zero-propagation / simplicity argument. -/

open QAlgorithms

namespace C1Spec

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the real quadratic form `w ↦ Re ⟨w, M w⟩`. -/
noncomputable def Q (M : Matrix ι ι ℂ) (w : EuclideanSpace ℂ ι) : ℝ :=
  RCLike.re (inner ℂ w (act M w))

lemma act_eq (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act A v = Matrix.toEuclideanLin A v := by
  rfl

lemma act_sub (A : Matrix ι ι ℂ) (u w : EuclideanSpace ℂ ι) :
    act A (u - w) = act A u - act A w := by
  rw [act_eq, act_eq, act_eq, map_sub]

lemma act_smul (A : Matrix ι ι ℂ) (c : ℂ) (u : EuclideanSpace ℂ ι) :
    act A (c • u) = c • act A u := by
  rw [act_eq, act_eq, map_smul]

section Spectral

variable {A : Matrix ι ι ℂ} (hA : A.IsHermitian)

lemma hT {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : (Matrix.toEuclideanLin A).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA

/-- the sorted (decreasing) orthonormal eigenbasis, indexed like `eigenvalues₀`. -/
noncomputable def B {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : OrthonormalBasis (Fin (Fintype.card ι)) ℂ (EuclideanSpace ℂ ι) :=
  (hT hA).eigenvectorBasis finrank_euclideanSpace

lemma B_eig (i : Fin (Fintype.card ι)) :
    act A (B hA i) = (hA.eigenvalues₀ i : ℂ) • B hA i := by
  rw [act_eq]
  exact (hT hA).apply_eigenvectorBasis finrank_euclideanSpace i

lemma repr_act (v : EuclideanSpace ℂ ι) (i : Fin (Fintype.card ι)) :
    (B hA).repr (act A v) i = (hA.eigenvalues₀ i : ℂ) * (B hA).repr v i := by
  rw [act_eq]
  exact (hT hA).eigenvectorBasis_apply_self_apply finrank_euclideanSpace v i

lemma norm_sq_expand (v : EuclideanSpace ℂ ι) :
    ‖v‖ ^ 2 = ∑ i, ‖(B hA).repr v i‖ ^ 2 := by
  rw [← (B hA).repr.norm_map v, EuclideanSpace.norm_sq_eq]

lemma quad_expand (v : EuclideanSpace ℂ ι) :
    Q A v = ∑ i, hA.eigenvalues₀ i * ‖(B hA).repr v i‖ ^ 2 := by
  unfold Q
  rw [← (B hA).repr.inner_map_map v (act A v), PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_act hA v i, ← smul_eq_mul, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow, ← Complex.ofReal_mul]

/-- lower Rayleigh bound from the eigenvalues that occur in `v`. -/
lemma quad_ge (c : ℝ) (v : EuclideanSpace ℂ ι)
    (h : ∀ i, (B hA).repr v i ≠ 0 → c ≤ hA.eigenvalues₀ i) : c * ‖v‖ ^ 2 ≤ Q A v := by
  rw [quad_expand hA, norm_sq_expand hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : (B hA).repr v i = 0
  · simp [hi]
  · exact mul_le_mul_of_nonneg_right (h i hi) (by positivity)

/-- upper Rayleigh bound from the eigenvalues that occur in `v`. -/
lemma quad_le (c : ℝ) (v : EuclideanSpace ℂ ι)
    (h : ∀ i, (B hA).repr v i ≠ 0 → hA.eigenvalues₀ i ≤ c) : Q A v ≤ c * ‖v‖ ^ 2 := by
  rw [quad_expand hA, norm_sq_expand hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : (B hA).repr v i = 0
  · simp [hi]
  · exact mul_le_mul_of_nonneg_right (h i hi) (by positivity)

lemma Q_B (i : Fin (Fintype.card ι)) : Q A (B hA i) = hA.eigenvalues₀ i := by
  unfold Q
  rw [B_eig hA i, inner_smul_right, inner_self_eq_norm_sq_to_K, (B hA).orthonormal.1 i]
  simp

include hA in
/-- a vector attaining a lower Rayleigh bound is an eigenvector. -/
lemma eig_of_min (lam : ℝ) (hmin : ∀ w : EuclideanSpace ℂ ι, lam * ‖w‖ ^ 2 ≤ Q A w)
    (w : EuclideanSpace ℂ ι) (hw : Q A w ≤ lam * ‖w‖ ^ 2) : act A w = (lam : ℂ) • w := by
  have hle : ∀ i, lam ≤ hA.eigenvalues₀ i := fun i => by
    have := hmin (B hA i)
    rwa [Q_B hA i, (B hA).orthonormal.1 i, one_pow, mul_one] at this
  rw [quad_expand hA, norm_sq_expand hA, Finset.mul_sum, ← sub_nonpos,
    ← Finset.sum_sub_distrib] at hw
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ hA.eigenvalues₀ i * ‖(B hA).repr w i‖ ^ 2 -
      lam * ‖(B hA).repr w i‖ ^ 2 := fun i _ => by
    rw [← sub_mul]; exact mul_nonneg (sub_nonneg.2 (hle i)) (by positivity)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hterm).1
    (le_antisymm hw (Finset.sum_nonneg hterm))
  apply (B hA).repr.injective
  ext i
  rw [repr_act hA w i, LinearIsometryEquiv.map_smul, PiLp.smul_apply, smul_eq_mul]
  have hi := h0 i (Finset.mem_univ _)
  rw [← sub_mul, mul_eq_zero] at hi
  rcases hi with hi | hi
  · rw [sub_eq_zero.1 hi]
  · have : (B hA).repr w i = 0 := by simpa using hi
    rw [this, mul_zero, mul_zero]

end Spectral

/-! ### Perron-Frobenius -/

lemma Q_sum (A : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι) :
    Q A u = ∑ x, ∑ y, (starRingEnd ℂ (u x) * (A x y * u y)).re := by
  simp [Q, act, PiLp.inner_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

lemma term_le (a p q : ℂ) (diag : Prop) [Decidable diag] (hpq : diag → p = q)
    (hoff : ¬ diag → a.im = 0 ∧ a.re ≤ 0) :
    (starRingEnd ℂ ((‖p‖ : ℝ) : ℂ) * (a * ((‖q‖ : ℝ) : ℂ))).re ≤
      (starRingEnd ℂ p * (a * q)).re := by
  by_cases hd : diag
  · obtain rfl := hpq hd
    apply le_of_eq
    have e1 : starRingEnd ℂ p * (a * p) = a * ((‖p‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, ← Complex.conj_mul']; ring
    have e2 : starRingEnd ℂ ((‖p‖ : ℝ) : ℂ) * (a * ((‖p‖ : ℝ) : ℂ)) =
        a * ((‖p‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_ofReal]; push_cast; ring
    rw [e1, e2]
  · obtain ⟨him, hre⟩ := hoff hd
    have ha : a = ((a.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [ha, Complex.conj_ofReal]
    have l1 : (((‖p‖ : ℝ) : ℂ) * (((a.re : ℝ) : ℂ) * ((‖q‖ : ℝ) : ℂ))).re =
        a.re * (‖p‖ * ‖q‖) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
    have l2 : (starRingEnd ℂ p * (((a.re : ℝ) : ℂ) * q)).re =
        a.re * (starRingEnd ℂ p * q).re := by
      rw [mul_left_comm, Complex.re_ofReal_mul]
    rw [l1, l2]
    apply mul_le_mul_of_nonpos_left _ hre
    calc (starRingEnd ℂ p * q).re ≤ ‖starRingEnd ℂ p * q‖ := Complex.re_le_norm _
      _ = ‖p‖ * ‖q‖ := by rw [norm_mul, Complex.norm_conj]

/-- the entrywise modulus of a vector. -/
noncomputable def absV (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun x => ((‖v x‖ : ℝ) : ℂ))

lemma absV_apply (v : EuclideanSpace ℂ ι) (x : ι) : absV v x = ((‖v x‖ : ℝ) : ℂ) := rfl

lemma norm_absV (v : EuclideanSpace ℂ ι) : ‖absV v‖ = ‖v‖ := by
  have h : ‖absV v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [absV_apply, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

lemma Q_absV_le (A : Matrix ι ι ℂ) (hoff : ∀ x y, x ≠ y → (A x y).im = 0 ∧ (A x y).re ≤ 0)
    (v : EuclideanSpace ℂ ι) : Q A (absV v) ≤ Q A v := by
  rw [Q_sum, Q_sum]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  rw [absV_apply, absV_apply]
  exact term_le (A x y) (v x) (v y) (x = y) (fun h => by rw [h]) (hoff x y)

/-- Perron-Frobenius zero propagation: a bottom eigenvector (for the Rayleigh minimum `lam`) of a
matrix with nonpositive real off-diagonal entries and connected support vanishing at one point
vanishes everywhere. -/
lemma pf_zero (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (lam : ℝ) (adj : ι → ι → Prop)
    (hoff : ∀ x y, x ≠ y → (A x y).im = 0 ∧ (A x y).re ≤ 0)
    (hadj : ∀ x y, adj x y → x ≠ y ∧ A x y ≠ 0)
    (hconn : ∀ x y, Relation.ReflTransGen adj x y)
    (hmin : ∀ w : EuclideanSpace ℂ ι, lam * ‖w‖ ^ 2 ≤ Q A w)
    (v : EuclideanSpace ℂ ι) (hv : act A v = (lam : ℂ) • v) (x0 : ι) (h0 : v x0 = 0) :
    v = 0 := by
  set w := absV v with hwdef
  have hQv : Q A v = lam * ‖v‖ ^ 2 := by
    unfold Q
    rw [hv, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  have hwle : Q A w ≤ lam * ‖w‖ ^ 2 := by
    rw [hwdef, norm_absV, ← hQv]; exact Q_absV_le A hoff v
  have hwe : act A w = (lam : ℂ) • w := eig_of_min hA lam hmin w hwle
  -- zero set is closed under `adj`
  have step : ∀ x y, v x = 0 → adj x y → v y = 0 := by
    intro x y hx hxy
    obtain ⟨hne, hA0⟩ := hadj x y hxy
    have hcomp : (act A w) x = ∑ z, A x z * w z := by
      simp [act, Matrix.mulVec, dotProduct]
    have hzero : ∑ z, (A x z * w z).re = 0 := by
      rw [← Complex.re_sum, ← hcomp, hwe]
      simp [hwdef, absV_apply, hx]
    have hnp : ∀ z ∈ Finset.univ, (A x z * w z).re ≤ 0 := by
      intro z _
      rw [hwdef, absV_apply, Complex.re_mul_ofReal]
      by_cases hz : x = z
      · subst hz; simp [hx]
      · exact mul_nonpos_of_nonpos_of_nonneg (hoff x z hz).2 (norm_nonneg _)
    have hy := (Finset.sum_eq_zero_iff_of_nonpos hnp).1 hzero y (Finset.mem_univ _)
    rw [hwdef, absV_apply, Complex.re_mul_ofReal] at hy
    have hre : (A x y).re ≠ 0 := by
      intro hr
      exact hA0 (Complex.ext (by simpa using hr) (by simpa using (hoff x y hne).1))
    have : ‖v y‖ = 0 := by
      rcases mul_eq_zero.1 hy with h | h
      · exact absurd h hre
      · exact h
    exact norm_eq_zero.1 this
  have hall : ∀ y, v y = 0 := by
    intro y
    induction hconn x0 y with
    | refl => exact h0
    | tail _ hbc ih => exact step _ _ ih hbc
  ext y
  simp [hall y]

/-- simplicity: two orthonormal bottom eigenvectors are impossible under Perron-Frobenius. -/
lemma no_two (A : Matrix ι ι ℂ) (lam : ℝ)
    (hpf : ∀ v : EuclideanSpace ℂ ι, act A v = (lam : ℂ) • v → ∀ x0, v x0 = 0 → v = 0)
    (u w : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (horth : inner ℂ u w = 0)
    (heu : act A u = (lam : ℂ) • u) (hew : act A w = (lam : ℂ) • w) : False := by
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  obtain ⟨x0, hx0⟩ : ∃ x0, u x0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu0 (by ext x; simp [hc x])
  set v := w x0 • u - u x0 • w with hvdef
  have hve : act A v = (lam : ℂ) • v := by
    rw [hvdef, act_sub, act_smul, act_smul, heu, hew, smul_sub, smul_comm (w x0),
      smul_comm (u x0)]
  have hv0 : v x0 = 0 := by
    rw [hvdef]; simp [mul_comm]
  have hv := hpf v hve x0 hv0
  rw [hvdef, sub_eq_zero] at hv
  have h1 : inner ℂ u (w x0 • u) = inner ℂ u (u x0 • w) := by rw [hv]
  rw [inner_smul_right, inner_smul_right, horth, inner_self_eq_norm_sq_to_K, hu] at h1
  simp at h1
  rw [h1, zero_smul] at hv
  have := (smul_eq_zero.1 hv.symm).resolve_left hx0
  rw [this, norm_zero] at hw
  exact zero_ne_one hw

end C1Spec

/-! C1 infrastructure for 52c231a1: entries of the QAOA mixer, entries of the negated path,
hypercube connectivity. -/

open QAlgorithms

namespace C1Mix

lemma X_apply {n : ℕ} (j : Fin n) (y z : Qubits n) :
    Stabilizer.CliffordOp.mat (Stabilizer.CliffordOp.pauli j Stabilizer.Pauli.X) y z =
      if (∀ a, a ≠ j → y a = z a) ∧ y j ≠ z j then 1 else 0 := by
  have hr : ∀ a : Fin n, a ∉ Set.range (Stabilizer.wire1 j) ↔ a ≠ j := by
    intro a
    constructor
    · intro h ha
      exact h ⟨0, by rw [ha]; rfl⟩
    · rintro h ⟨b, hb⟩
      exact h (by rw [← hb]; rfl)
  have e : Stabilizer.CliffordOp.mat (Stabilizer.CliffordOp.pauli j Stabilizer.Pauli.X) y z =
      if ∀ a : Fin n, a ∉ Set.range (Stabilizer.wire1 j) → y a = z a then pauliX (y j) (z j)
      else 0 := rfl
  rw [e]
  by_cases h : ∀ a : Fin n, a ∉ Set.range (Stabilizer.wire1 j) → y a = z a
  · rw [if_pos h]
    have h' : ∀ a, a ≠ j → y a = z a := fun a ha => h a ((hr a).2 ha)
    by_cases hj : y j = z j
    · simp [pauliX, hj]
    · simp only [pauliX, Matrix.of_apply, if_neg hj]
      rw [if_pos ⟨h', hj⟩]
  · rw [if_neg h, if_neg]
    rintro ⟨h1, _⟩
    exact h fun a ha => h1 a ((hr a).1 ha)

lemma mixer_apply {n : ℕ} (y z : Qubits n) :
    qaoaMixer n y z =
      ∑ j : Fin n, (if (∀ a, a ≠ j → y a = z a) ∧ y j ≠ z j then (1 : ℂ) else 0) := by
  unfold qaoaMixer
  rw [Matrix.sum_apply]
  exact Finset.sum_congr rfl fun j _ => X_apply j y z

lemma mixer_im {n : ℕ} (y z : Qubits n) : (qaoaMixer n y z).im = 0 := by
  rw [mixer_apply, Complex.im_sum]
  exact Finset.sum_eq_zero fun j _ => by split_ifs <;> simp

lemma mixer_re_nonneg {n : ℕ} (y z : Qubits n) : 0 ≤ (qaoaMixer n y z).re := by
  rw [mixer_apply, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp

/-- hypercube adjacency: `z` is `y` with one bit flipped. -/
def adj {n : ℕ} (y z : Qubits n) : Prop := ∃ j, z = Function.update y j (!(y j))

lemma mixer_adj_pos {n : ℕ} (y z : Qubits n) (h : adj y z) : 0 < (qaoaMixer n y z).re := by
  obtain ⟨j, rfl⟩ := h
  rw [mixer_apply, Complex.re_sum]
  have hj : (∀ a, a ≠ j → y a = Function.update y j (!(y j)) a) ∧
      y j ≠ Function.update y j (!(y j)) j := by
    refine ⟨fun a ha => by rw [Function.update_of_ne ha], ?_⟩
    rw [Function.update_self]
    cases y j <;> decide
  calc (0 : ℝ) < 1 := one_pos
    _ = (if (∀ a, a ≠ j → y a = Function.update y j (!(y j)) a) ∧
          y j ≠ Function.update y j (!(y j)) j then (1 : ℂ) else 0).re := by rw [if_pos hj]; simp
    _ ≤ _ := Finset.single_le_sum (f := fun k : Fin n =>
          (if (∀ a, a ≠ k → y a = Function.update y j (!(y j)) a) ∧
            y k ≠ Function.update y j (!(y j)) k then (1 : ℂ) else 0).re)
          (fun k _ => by split_ifs <;> simp) (Finset.mem_univ j)

lemma adj_ne {n : ℕ} (y z : Qubits n) (h : adj y z) : y ≠ z := by
  obtain ⟨j, rfl⟩ := h
  intro he
  have := congrFun he j
  rw [Function.update_self] at this
  cases hy : y j <;> rw [hy] at this <;> simp at this

lemma hyper_conn {n : ℕ} (x y : Qubits n) : Relation.ReflTransGen adj x y := by
  suffices H : ∀ k : ℕ, ∀ x : Qubits n,
      (Finset.univ.filter fun j => x j ≠ y j).card = k → Relation.ReflTransGen adj x y from
    H _ x rfl
  intro k
  induction k with
  | zero =>
    intro x hx
    have : x = y := by
      funext j
      by_contra hj
      have : j ∈ Finset.univ.filter fun j => x j ≠ y j := by simp [hj]
      rw [Finset.card_eq_zero] at hx
      rw [hx] at this
      simp at this
    rw [this]
  | succ k ih =>
    intro x hx
    obtain ⟨j, hj⟩ : ∃ j, j ∈ Finset.univ.filter fun j => x j ≠ y j := by
      apply Finset.card_pos.1; omega
    have hxj : x j ≠ y j := by simpa using hj
    set x' := Function.update x j (!(x j)) with hx'
    have hx'j : x' j = y j := by
      rw [hx', Function.update_self]
      cases hx : x j <;> cases hy : y j <;> simp_all
    have hfil : (Finset.univ.filter fun i => x' i ≠ y i) =
        (Finset.univ.filter fun i => x i ≠ y i).erase j := by
      ext i
      by_cases hij : i = j
      · subst hij; simp [hx'j]
      · simp [hij, hx']
    have hcard : (Finset.univ.filter fun i => x' i ≠ y i).card = k := by
      rw [hfil, Finset.card_erase_of_mem hj]; omega
    exact Relation.ReflTransGen.head ⟨j, rfl⟩ (ih x' hcard)

end C1Mix

/-! ### C1: the generic uniform-gap argument and the assembly -/

namespace C1Gen

open C1Spec

/-- index of the smallest eigenvalue (`eigenvalues₀` is decreasing). -/
def j1 (ι : Type) [Fintype ι] (h : 0 < Fintype.card ι) : Fin (Fintype.card ι) :=
  ⟨Fintype.card ι - 1, by omega⟩

/-- index of the second smallest eigenvalue. -/
def j2 (ι : Type) [Fintype ι] (h : 1 < Fintype.card ι) : Fin (Fintype.card ι) :=
  ⟨Fintype.card ι - 2, by omega⟩

section Gen

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma le_j1 (h : 0 < Fintype.card ι) (i : Fin (Fintype.card ι)) : i ≤ j1 ι h := by
  rw [Fin.le_iff_val_le_val]
  show (i : ℕ) ≤ Fintype.card ι - 1
  have := i.isLt
  omega

lemma le_j2 (h : 0 < Fintype.card ι) (h2 : 1 < Fintype.card ι) (i : Fin (Fintype.card ι))
    (hi : i ≠ j1 ι h) : i ≤ j2 ι h2 := by
  rw [Fin.le_iff_val_le_val]
  show (i : ℕ) ≤ Fintype.card ι - 2
  have := i.isLt
  have : (i : ℕ) ≠ Fintype.card ι - 1 := fun e => hi (Fin.ext e)
  omega

lemma j2_ne (h : 0 < Fintype.card ι) (h2 : 1 < Fintype.card ι) : j2 ι h2 ≠ j1 ι h := by
  intro e
  have := congrArg Fin.val e
  simp only [j1, j2] at this
  omega

lemma eq_j1 (h : 0 < Fintype.card ι) (h2 : ¬ 1 < Fintype.card ι) (i : Fin (Fintype.card ι)) :
    i = j1 ι h := by
  apply Fin.ext
  show (i : ℕ) = Fintype.card ι - 1
  have := i.isLt
  omega

lemma herm_rsmul (c : ℝ) {D : Matrix ι ι ℂ} (hD : D.IsHermitian) :
    ((c : ℂ) • D).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hD.eq]
  simp [Complex.conj_ofReal]

lemma herm_path {A D : Matrix ι ι ℂ} (hA : A.IsHermitian) (hD : D.IsHermitian) (s : ℝ) :
    (A + (s : ℂ) • D).IsHermitian :=
  hA.add (herm_rsmul s hD)

lemma Q_add (A D : Matrix ι ι ℂ) (s : ℝ) (w : EuclideanSpace ℂ ι) :
    Q (A + (s : ℂ) • D) w = Q A w + s * Q D w := by
  have e : act (A + (s : ℂ) • D) w = act A w + (s : ℂ) • act D w := by
    rw [act_eq, act_eq, act_eq, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  unfold Q
  rw [e, inner_add_right, inner_smul_right, map_add]
  simp

lemma Q_bound (D : Matrix ι ι ℂ) (hD : D.IsHermitian) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w, |Q D w| ≤ K * ‖w‖ ^ 2 := by
  refine ⟨∑ i, |hD.eigenvalues₀ i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun w => ?_⟩
  have hi : ∀ i, |hD.eigenvalues₀ i| ≤ ∑ i, |hD.eigenvalues₀ i| := fun i =>
    Finset.single_le_sum (f := fun i => |hD.eigenvalues₀ i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
  rw [abs_le]
  constructor
  · have := quad_ge hD (-(∑ i, |hD.eigenvalues₀ i|)) w (fun i _ => by
      have h1 := hi i
      have h2 := neg_abs_le (hD.eigenvalues₀ i)
      linarith)
    linarith
  · exact quad_le hD _ w (fun i _ => le_trans (le_abs_self _) (hi i))

lemma ray_min {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (h : 0 < Fintype.card ι)
    (w : EuclideanSpace ℂ ι) : hH.eigenvalues₀ (j1 ι h) * ‖w‖ ^ 2 ≤ Q H w :=
  quad_ge hH _ w fun i _ => hH.eigenvalues₀_antitone (le_j1 h i)

lemma strict {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (h : 0 < Fintype.card ι)
    (h2 : 1 < Fintype.card ι)
    (hpf : ∀ v : EuclideanSpace ℂ ι, act H v = ((hH.eigenvalues₀ (j1 ι h) : ℝ) : ℂ) • v →
      ∀ x0, v x0 = 0 → v = 0) :
    hH.eigenvalues₀ (j1 ι h) < hH.eigenvalues₀ (j2 ι h2) := by
  refine lt_of_le_of_ne (hH.eigenvalues₀_antitone (le_j1 h _)) fun heq => ?_
  exact no_two H _ hpf (B hH (j1 ι h)) (B hH (j2 ι h2)) ((B hH).orthonormal.1 _)
    ((B hH).orthonormal.1 _) ((B hH).orthonormal.2 (j2_ne h h2).symm) (B_eig hH _)
    (by rw [B_eig hH, ← heq])

lemma lip1 (A D : Matrix ι ι ℂ) (hp : ∀ s : ℝ, (A + (s : ℂ) • D).IsHermitian)
    (h : 0 < Fintype.card ι) (K : ℝ) (hK : ∀ w, |Q D w| ≤ K * ‖w‖ ^ 2) (s t : ℝ) :
    (hp s).eigenvalues₀ (j1 ι h) ≤ (hp t).eigenvalues₀ (j1 ι h) + K * |s - t| := by
  have hb : ‖B (hp t) (j1 ι h)‖ = 1 := (B (hp t)).orthonormal.1 _
  have h1 := ray_min (hp s) h (B (hp t) (j1 ι h))
  have h2 := Q_B (hp t) (j1 ι h)
  have h3 := hK (B (hp t) (j1 ι h))
  rw [Q_add] at h1 h2
  rw [hb, one_pow, mul_one] at h1 h3
  have h4 : (s - t) * Q D (B (hp t) (j1 ι h)) ≤ K * |s - t| := by
    calc (s - t) * Q D (B (hp t) (j1 ι h)) ≤ |(s - t) * Q D (B (hp t) (j1 ι h))| :=
          le_abs_self _
      _ = |s - t| * |Q D (B (hp t) (j1 ι h))| := abs_mul _ _
      _ ≤ |s - t| * K := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = K * |s - t| := mul_comm _ _
  linarith

lemma perp2 (a b : ℂ) : ∃ α β : ℂ, (α ≠ 0 ∨ β ≠ 0) ∧ α * a + β * b = 0 := by
  by_cases hb : b = 0
  · exact ⟨0, 1, Or.inr one_ne_zero, by simp [hb]⟩
  · exact ⟨b, -a, Or.inl hb, by ring⟩

lemma lip2 (A D : Matrix ι ι ℂ) (hp : ∀ s : ℝ, (A + (s : ℂ) • D).IsHermitian)
    (h : 0 < Fintype.card ι) (h2 : 1 < Fintype.card ι) (K : ℝ)
    (hK : ∀ w, |Q D w| ≤ K * ‖w‖ ^ 2) (s t : ℝ) :
    (hp s).eigenvalues₀ (j2 ι h2) ≤ (hp t).eigenvalues₀ (j2 ι h2) + K * |s - t| := by
  obtain ⟨α, β, hαβ, hab⟩ := perp2 (inner ℂ (B (hp s) (j1 ι h)) (B (hp t) (j1 ι h)))
    (inner ℂ (B (hp s) (j1 ι h)) (B (hp t) (j2 ι h2)))
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℂ ι,
      v = α • B (hp t) (j1 ι h) + β • B (hp t) (j2 ι h2) := ⟨_, rfl⟩
  have hne := j2_ne h h2
  have hrt : ∀ i, (B (hp t)).repr v i =
      (if i = j1 ι h then α else 0) + (if i = j2 ι h2 then β else 0) := by
    intro i
    rw [hv, map_add, map_smul, map_smul, OrthonormalBasis.repr_self,
      OrthonormalBasis.repr_self]
    simp [EuclideanSpace.single_apply]
  have hrs : (B (hp s)).repr v (j1 ι h) = 0 := by
    rw [OrthonormalBasis.repr_apply_apply, hv, inner_add_right, inner_smul_right,
      inner_smul_right]
    exact hab
  have hv0 : v ≠ 0 := by
    intro h0
    rcases hαβ with hα | hβ
    · have := hrt (j1 ι h)
      simp [h0, hne.symm] at this
      exact hα (by simpa [eq_comm] using this)
    · have := hrt (j2 ι h2)
      simp [h0, hne] at this
      exact hβ (by simpa [eq_comm] using this)
  have hpos : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv0) 2
  have hlow := quad_ge (hp s) ((hp s).eigenvalues₀ (j2 ι h2)) v (fun i hi => by
    by_cases hi1 : i = j1 ι h
    · subst hi1; exact absurd hrs hi
    · exact (hp s).eigenvalues₀_antitone (le_j2 h h2 i hi1))
  have hup := quad_le (hp t) ((hp t).eigenvalues₀ (j2 ι h2)) v (fun i hi => by
    rw [hrt] at hi
    by_cases hi1 : i = j1 ι h
    · subst hi1; exact (hp t).eigenvalues₀_antitone (le_j1 h _)
    · by_cases hi2 : i = j2 ι h2
      · subst hi2; exact le_rfl
      · simp [hi1, hi2] at hi)
  rw [Q_add] at hlow hup
  have h3 := hK v
  have h4 : (s - t) * Q D v ≤ K * |s - t| * ‖v‖ ^ 2 := by
    calc (s - t) * Q D v ≤ |(s - t) * Q D v| := le_abs_self _
      _ = |s - t| * |Q D v| := abs_mul _ _
      _ ≤ |s - t| * (K * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = K * |s - t| * ‖v‖ ^ 2 := by ring
  by_contra hc
  push_neg at hc
  have := mul_lt_mul_of_pos_right hc hpos
  linarith

lemma gap_at (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (h : 0 < Fintype.card ι) (γ : ℝ)
    (hγ : 0 < γ)
    (hg : ∀ i, i ≠ j1 ι h → hH.eigenvalues₀ (j1 ι h) + γ ≤ hH.eigenvalues₀ i) :
    HasGapAround H (hH.eigenvalues₀ (j1 ι h)) γ := by
  unfold HasGapAround ascEigenvalues
  rw [dif_pos hH]
  refine ⟨hH, ⟨Fin.rev (j1 ι h), by simp, fun k hk => ?_⟩, fun k hk => ?_⟩
  · have hk2 : hH.eigenvalues₀ (Fin.rev k) = hH.eigenvalues₀ (j1 ι h) := hk
    by_contra hne
    have hk' : Fin.rev k ≠ j1 ι h := fun e => hne (by rw [← e, Fin.rev_rev])
    have := hg _ hk'
    linarith
  · have hk2 : hH.eigenvalues₀ (Fin.rev k) ≠ hH.eigenvalues₀ (j1 ι h) := hk
    have hk' : Fin.rev k ≠ j1 ι h := fun e => hk2 (by rw [e])
    have := hg _ hk'
    show γ ≤ |hH.eigenvalues₀ (Fin.rev k) - hH.eigenvalues₀ (j1 ι h)|
    rw [le_abs]
    left
    linarith

lemma unif_gap (A D : Matrix ι ι ℂ) (hp : ∀ s : ℝ, (A + (s : ℂ) • D).IsHermitian)
    (h : 0 < Fintype.card ι) (hD : D.IsHermitian)
    (hstr : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ h2 : 1 < Fintype.card ι,
      (hp s).eigenvalues₀ (j1 ι h) < (hp s).eigenvalues₀ (j2 ι h2)) :
    ContinuousOn (fun s => (hp s).eigenvalues₀ (j1 ι h)) (Set.Icc 0 1) ∧
    ∃ γ : ℝ, 0 < γ ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i, i ≠ j1 ι h →
      (hp s).eigenvalues₀ (j1 ι h) + γ ≤ (hp s).eigenvalues₀ i := by
  obtain ⟨K, _, hK⟩ := Q_bound D hD
  have c1 : Continuous (fun s => (hp s).eigenvalues₀ (j1 ι h)) :=
    (LipschitzWith.of_le_add_mul' (f := fun s => (hp s).eigenvalues₀ (j1 ι h)) K
      fun x y => by rw [Real.dist_eq]; exact lip1 A D hp h K hK x y).continuous
  refine ⟨c1.continuousOn, ?_⟩
  by_cases h2 : 1 < Fintype.card ι
  · have c2 : Continuous (fun s => (hp s).eigenvalues₀ (j2 ι h2)) :=
      (LipschitzWith.of_le_add_mul' (f := fun s => (hp s).eigenvalues₀ (j2 ι h2)) K
        fun x y => by rw [Real.dist_eq]; exact lip2 A D hp h h2 K hK x y).continuous
    obtain ⟨s1, hs1, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one)
      (c2.sub c1).continuousOn
    refine ⟨(hp s1).eigenvalues₀ (j2 ι h2) - (hp s1).eigenvalues₀ (j1 ι h),
      sub_pos.2 (hstr s1 hs1 h2), fun s hs i hi => ?_⟩
    have hm : (hp s1).eigenvalues₀ (j2 ι h2) - (hp s1).eigenvalues₀ (j1 ι h) ≤
        (hp s).eigenvalues₀ (j2 ι h2) - (hp s).eigenvalues₀ (j1 ι h) :=
      isMinOn_iff.1 hmin s hs
    have := (hp s).eigenvalues₀_antitone (le_j2 h h2 i hi)
    linarith
  · exact ⟨1, one_pos, fun s _ i hi => absurd (eq_j1 h h2 i) hi⟩

lemma inner_absV_ne (u b : EuclideanSpace ℂ ι) (r : ι → ℝ) (hr : ∀ x, 0 < r x)
    (hur : ∀ x, u x = (r x : ℂ)) (hb : b ≠ 0) : inner ℂ u (absV b) ≠ 0 := by
  have e : inner ℂ u (absV b) = ((∑ x, r x * ‖b x‖ : ℝ) : ℂ) := by
    rw [PiLp.inner_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [absV_apply, hur]
    simp [Complex.ofReal_mul, mul_comm]
  rw [e, Complex.ofReal_ne_zero]
  obtain ⟨x0, hx0⟩ : ∃ x, b x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hb (by ext x; simp [hc x])
  exact (Finset.sum_pos' (fun x _ => mul_nonneg (hr x).le (norm_nonneg _))
    ⟨x0, Finset.mem_univ _, mul_pos (hr x0) (norm_pos_iff.2 hx0)⟩).ne'

theorem gen [Nonempty ι] (A D : Matrix ι ι ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    (adj : ι → ι → Prop)
    (hoff : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y, x ≠ y →
      ((A + (s : ℂ) • D) x y).im = 0 ∧ ((A + (s : ℂ) • D) x y).re ≤ 0)
    (hadj : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y, adj x y → x ≠ y ∧ (A + (s : ℂ) • D) x y ≠ 0)
    (hconn : ∀ x y, Relation.ReflTransGen adj x y)
    (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) (r : ι → ℝ) (hr : ∀ x, 0 < r x)
    (hur : ∀ x, u x = (r x : ℂ)) (μ : ℝ) (hμ : act A u = (μ : ℂ) • u) :
    ∃ (lam : ℝ → ℝ) (φ : ℝ → EuclideanSpace ℂ ι) (γ : ℝ), 0 < γ ∧
      ContinuousOn lam (Set.Icc 0 1) ∧ φ 0 = u ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧
        act (A + (s : ℂ) • D) (φ s) = (lam s : ℂ) • φ s ∧
        HasGapAround (A + (s : ℂ) • D) (lam s) γ ∧
        ∀ v : EuclideanSpace ℂ ι, lam s * ‖v‖ ^ 2 ≤ Q (A + (s : ℂ) • D) v := by
  have h : 0 < Fintype.card ι := Fintype.card_pos
  have hp : ∀ s : ℝ, (A + (s : ℂ) • D).IsHermitian := herm_path hA hD
  have hpf : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ v : EuclideanSpace ℂ ι,
      act (A + (s : ℂ) • D) v = (((hp s).eigenvalues₀ (j1 ι h) : ℝ) : ℂ) • v →
      ∀ x0, v x0 = 0 → v = 0 := fun s hs v hv x0 hx0 =>
    pf_zero _ (hp s) _ adj (hoff s hs) (hadj s hs) hconn (ray_min (hp s) h) v hv x0 hx0
  obtain ⟨hcont, γ, hγ, hgap⟩ := unif_gap A D hp h hD
    (fun s hs h2 => strict (hp s) h h2 (hpf s hs))
  have h00 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hM0 : A + ((0 : ℝ) : ℂ) • D = A := by simp
  have hμ' : act (A + ((0 : ℝ) : ℂ) • D) u = (μ : ℂ) • u := by rw [hM0]; exact hμ
  have hμ0 : μ = (hp 0).eigenvalues₀ (j1 ι h) := by
    have hb1 : ‖B (hp 0) (j1 ι h)‖ = 1 := (B (hp 0)).orthonormal.1 _
    have hb0 : B (hp 0) (j1 ι h) ≠ 0 := fun e => by
      rw [e, norm_zero] at hb1; exact zero_ne_one hb1
    have hwe : act (A + ((0 : ℝ) : ℂ) • D) (absV (B (hp 0) (j1 ι h))) =
        (((hp 0).eigenvalues₀ (j1 ι h) : ℝ) : ℂ) • absV (B (hp 0) (j1 ι h)) := by
      refine eig_of_min (hp 0) _ (ray_min (hp 0) h) _ ?_
      rw [norm_absV, hb1, one_pow, mul_one, ← Q_B (hp 0) (j1 ι h)]
      exact Q_absV_le _ (hoff 0 h00) _
    have hsym := (hT (hp 0)) u (absV (B (hp 0) (j1 ι h)))
    rw [← act_eq, ← act_eq, hwe, hμ', inner_smul_left, inner_smul_right,
      Complex.conj_ofReal] at hsym
    have hne := inner_absV_ne u _ r hr hur hb0
    exact_mod_cast mul_right_cancel₀ hne hsym
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ → ℝ, ∀ s, lam s = (hp s).eigenvalues₀ (j1 ι h) :=
    ⟨_, fun s => rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → EuclideanSpace ℂ ι,
      ∀ s, φ s = if s = 0 then u else B (hp s) (j1 ι h) := ⟨_, fun s => rfl⟩
  have hlamf : lam = fun s => (hp s).eigenvalues₀ (j1 ι h) := funext hlam
  refine ⟨lam, φ, γ, hγ, by rw [hlamf]; exact hcont, by rw [hφ, if_pos rfl],
    fun s hs => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hφ]
    by_cases h0 : s = 0
    · rw [if_pos h0]; exact hu
    · rw [if_neg h0]; exact (B (hp s)).orthonormal.1 _
  · rw [hφ, hlam]
    by_cases h0 : s = 0
    · subst h0; rw [if_pos rfl, hμ', hμ0]
    · rw [if_neg h0]; exact B_eig (hp s) _
  · rw [hlam]; exact gap_at _ (hp s) h γ hγ (hgap s hs)
  · rw [hlam]; exact ray_min (hp s) h

end Gen

end C1Gen

namespace C1Main

open C1Spec C1Mix C1Gen

lemma mixer_herm (n : ℕ) : (qaoaMixer n).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  have hre : star (qaoaMixer n j i) = qaoaMixer n j i :=
    Complex.ext (by simp) (by simp [mixer_im j i])
  rw [hre, mixer_apply, mixer_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases ha : (∀ a, a ≠ k → j a = i a) ∧ j k ≠ i k
  · rw [if_pos ha, if_pos ⟨fun a h => (ha.1 a h).symm, Ne.symm ha.2⟩]
  · by_cases hb : (∀ a, a ≠ k → i a = j a) ∧ i k ≠ j k
    · exact absurd ⟨fun a h => (hb.1 a h).symm, Ne.symm hb.2⟩ ha
    · rw [if_neg ha, if_neg hb]

lemma prob_herm {n : ℕ} (f : Qubits n → ℝ) : (problemHamiltonian f).IsHermitian := by
  unfold Matrix.IsHermitian problemHamiltonian
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext z
  simp

lemma path_eq {n : ℕ} (f : Qubits n → ℝ) (s0 s : ℝ) :
    linInterp (-qaoaMixer n) (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) s =
      -qaoaMixer n + (s : ℂ) •
        (-linInterp (qaoaMixer n) (problemHamiltonian f) s0 + qaoaMixer n) := by
  show ((1 - s : ℝ) : ℂ) • (-qaoaMixer n) +
      (s : ℂ) • (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) = _
  simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, smul_add, smul_neg]
  abel

lemma entry {n : ℕ} (f : Qubits n → ℝ) (s0 s : ℝ) (x y : Qubits n) (hxy : x ≠ y) :
    (-qaoaMixer n + (s : ℂ) •
        (-linInterp (qaoaMixer n) (problemHamiltonian f) s0 + qaoaMixer n)) x y =
      ((-(1 - s * s0) : ℝ) : ℂ) * qaoaMixer n x y := by
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, linInterp,
    problemHamiltonian, Matrix.diagonal_apply_ne _ hxy, smul_eq_mul, mul_zero, add_zero]
  push_cast
  ring

lemma flip_iff {n : ℕ} (j : Fin n) (y z : Qubits n) :
    ((∀ a, a ≠ j → y a = z a) ∧ y j ≠ z j) ↔ z = Function.update y j (!(y j)) := by
  constructor
  · rintro ⟨h1, h2⟩
    funext a
    by_cases ha : a = j
    · subst ha
      rw [Function.update_self]
      cases hy : y a <;> cases hz : z a <;> simp_all
    · rw [Function.update_of_ne ha]
      exact (h1 a ha).symm
  · rintro rfl
    refine ⟨fun a ha => by rw [Function.update_of_ne ha], ?_⟩
    rw [Function.update_self]
    cases y j <;> decide

lemma mixer_rowsum {n : ℕ} (y : Qubits n) : ∑ z, qaoaMixer n y z = (n : ℂ) := by
  simp_rw [mixer_apply]
  rw [Finset.sum_comm]
  simp_rw [flip_iff]
  simp

lemma had_apply (n : ℕ) (x : Qubits n) :
    act (hadamardN n) (zeroKet n) x = (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) := by
  have hd : dotBits (fun _ : Fin n => false) x = false := by
    unfold dotBits
    simp only [Bool.false_and]
    exact Finset.sum_const_zero
  simp [act, zeroKet, ket, hadamardN, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply,
    hd]

lemma had_norm (n : ℕ) : ‖act (hadamardN n) (zeroKet n)‖ = 1 := by
  have hsq : ((Real.sqrt 2)⁻¹ ^ n) ^ 2 = ((1 : ℝ) / 2) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul, inv_pow, Real.sq_sqrt (by norm_num)]
    ring
  have h : ‖act (hadamardN n) (zeroKet n)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [had_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsq]
    simp [Fintype.card_fun, ← mul_pow]
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [h, one_pow])

lemma had_eig (n : ℕ) : act (qaoaMixer n) (act (hadamardN n) (zeroKet n)) =
    ((n : ℝ) : ℂ) • act (hadamardN n) (zeroKet n) := by
  ext y
  have e1 : act (qaoaMixer n) (act (hadamardN n) (zeroKet n)) y =
      ∑ z, qaoaMixer n y z * act (hadamardN n) (zeroKet n) z := by
    simp only [act, Matrix.mulVec, dotProduct]
  rw [e1]
  simp only [had_apply]
  rw [← Finset.sum_mul, mixer_rowsum]
  simp [had_apply]

theorem c1_main (n : ℕ) (f : Qubits n → ℝ) (s0 : ℝ) (hs0 : s0 ∈ Set.Ico (0 : ℝ) 1) :
    ∃ (lam : ℝ → ℝ) (φ : ℝ → EuclideanSpace ℂ (Qubits n)) (γ : ℝ), 0 < γ ∧
      ContinuousOn lam (Set.Icc 0 1) ∧ φ 0 = act (hadamardN n) (zeroKet n) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsState (φ s) ∧
        act (linInterp (-qaoaMixer n) (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) s)
          (φ s) = (lam s : ℂ) • φ s ∧
        HasGapAround
          (linInterp (-qaoaMixer n) (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) s)
          (lam s) γ ∧
        ∀ v : EuclideanSpace ℂ (Qubits n), lam s * ‖v‖ ^ 2 ≤ RCLike.re (inner ℂ v
          (act (linInterp (-qaoaMixer n) (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) s)
            v)) := by
  have hX : (qaoaMixer n).IsHermitian := mixer_herm n
  have hLh : (linInterp (qaoaMixer n) (problemHamiltonian f) s0).IsHermitian :=
    (herm_rsmul (1 - s0) hX).add (herm_rsmul s0 (prob_herm f))
  have hcoef : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < 1 - s * s0 := fun s hs => by
    have : s * s0 ≤ s0 := mul_le_of_le_one_left hs0.1 hs.2
    linarith [hs0.2]
  have hoff : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y, x ≠ y →
      ((-qaoaMixer n + (s : ℂ) •
        (-linInterp (qaoaMixer n) (problemHamiltonian f) s0 + qaoaMixer n)) x y).im = 0 ∧
      ((-qaoaMixer n + (s : ℂ) •
        (-linInterp (qaoaMixer n) (problemHamiltonian f) s0 + qaoaMixer n)) x y).re ≤ 0 := by
    intro s hs x y hxy
    rw [entry f s0 s x y hxy, Complex.re_ofReal_mul, Complex.im_ofReal_mul, mixer_im, mul_zero]
    exact ⟨rfl, mul_nonpos_of_nonpos_of_nonneg (by linarith [hcoef s hs])
      (mixer_re_nonneg x y)⟩
  have hadj : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y, adj x y → x ≠ y ∧
      (-qaoaMixer n + (s : ℂ) •
        (-linInterp (qaoaMixer n) (problemHamiltonian f) s0 + qaoaMixer n)) x y ≠ 0 := by
    intro s hs x y hxy
    refine ⟨adj_ne x y hxy, ?_⟩
    rw [entry f s0 s x y (adj_ne x y hxy)]
    intro h0
    have h3 := congrArg Complex.re h0
    rw [Complex.re_ofReal_mul, Complex.zero_re] at h3
    have h1 := mixer_adj_pos x y hxy
    have h2 := hcoef s hs
    nlinarith [mul_pos h2 h1]
  have hμ : act (-qaoaMixer n) (act (hadamardN n) (zeroKet n)) =
      ((-(n : ℝ) : ℝ) : ℂ) • act (hadamardN n) (zeroKet n) := by
    rw [act_eq, map_neg, LinearMap.neg_apply, ← act_eq, had_eig, Complex.ofReal_neg, neg_smul]
  obtain ⟨lam, φ, γ, hγ, hc, hφ0, hall⟩ := gen (-qaoaMixer n)
    (-linInterp (qaoaMixer n) (problemHamiltonian f) s0 + qaoaMixer n) hX.neg (hLh.neg.add hX)
    adj hoff hadj hyper_conn (act (hadamardN n) (zeroKet n)) (had_norm n)
    (fun _ => (Real.sqrt 2)⁻¹ ^ n)
    (fun _ => pow_pos (inv_pos.2 (Real.sqrt_pos.2 two_pos)) n) (had_apply n) _ hμ
  refine ⟨lam, φ, γ, hγ, hc, hφ0, fun s hs => ?_⟩
  rw [path_eq]
  exact hall s hs

end C1Main

section C2Sec

/-! C2 for 52c231a1: a top eigenvector of `H(s0) = (1-s0) H_I + s0 H_F` is `δ`-close to a top
eigenvector of the diagonal `H_F` once `s0` is close to 1 (variational argument). -/

open QAlgorithms Set

namespace C2Aux

variable {ι : Type} [Fintype ι]

/-- the real quadratic form `w ↦ Re ⟨w, M w⟩`. -/
noncomputable def Q (M : Matrix ι ι ℂ) (w : EuclideanSpace ℂ ι) : ℝ :=
  RCLike.re (inner ℂ w (act M w))

lemma act_add (A B : Matrix ι ι ℂ) (w : EuclideanSpace ℂ ι) :
    act (A + B) w = act A w + act B w := by
  simp [act, Matrix.add_mulVec]

lemma act_smulM (c : ℂ) (A : Matrix ι ι ℂ) (w : EuclideanSpace ℂ ι) :
    act (c • A) w = c • act A w := by
  simp [act, Matrix.smul_mulVec]

lemma act_neg (A : Matrix ι ι ℂ) (w : EuclideanSpace ℂ ι) : act (-A) w = -act A w := by
  simp [act, Matrix.neg_mulVec]

lemma Q_neg (A : Matrix ι ι ℂ) (w : EuclideanSpace ℂ ι) : Q (-A) w = -Q A w := by
  simp [Q, act_neg, inner_neg_right]

lemma Q_lin (A B : Matrix ι ι ℂ) (s : ℝ) (w : EuclideanSpace ℂ ι) :
    Q (linInterp A B s) w = (1 - s) * Q A w + s * Q B w := by
  simp only [Q, linInterp, act_add, act_smulM, inner_add_right, inner_smul_right, map_add]
  simp [Complex.re_ofReal_mul]

/-- `act A` as a continuous ℂ-linear map. -/
noncomputable def actCLM (A : Matrix ι ι ℂ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := act A
      map_add' := fun x y => by simp [act, Matrix.mulVec_add]
      map_smul' := fun c x => by simp [act, Matrix.mulVec_smul] }

lemma Q_abs_le (A : Matrix ι ι ℂ) (w : EuclideanSpace ℂ ι) :
    |Q A w| ≤ ‖actCLM A‖ * ‖w‖ ^ 2 := by
  have h1 : |Q A w| ≤ ‖inner ℂ w (act A w)‖ := RCLike.abs_re_le_norm _
  have h2 : ‖inner ℂ w (act A w)‖ ≤ ‖w‖ * ‖act A w‖ := norm_inner_le_norm _ _
  have h3 : ‖act A w‖ ≤ ‖actCLM A‖ * ‖w‖ := (actCLM A).le_opNorm w
  have h4 : ‖w‖ * ‖act A w‖ ≤ ‖w‖ * (‖actCLM A‖ * ‖w‖) :=
    mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  nlinarith

variable [DecidableEq ι]

lemma Q_diag (f : ι → ℝ) (w : EuclideanSpace ℂ ι) :
    Q (Matrix.diagonal fun i => (f i : ℂ)) w = ∑ i, f i * ‖w i‖ ^ 2 := by
  simp only [Q, act, PiLp.inner_apply, Matrix.mulVec_diagonal, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.inner_apply, WithLp.ofLp_toLp]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end C2Aux

set_option maxHeartbeats 1000000 in
open C2Aux in
theorem c2_solution :
    ∀ (n : ℕ) (f : Qubits n → ℝ) (δ : ℝ), 0 < δ → ∃ s0 ∈ Set.Ico (0 : ℝ) 1,
      ∀ v : EuclideanSpace ℂ (Qubits n), IsState v → ∀ μ : ℝ,
        act (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) v = (μ : ℂ) • v →
        (∀ w : EuclideanSpace ℂ (Qubits n), μ * ‖w‖ ^ 2 ≤
          RCLike.re (inner ℂ w (act (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) w))) →
        ∃ φ : EuclideanSpace ℂ (Qubits n), IsState φ ∧
          act (problemHamiltonian f) φ =
            ((Finset.univ.sup' Finset.univ_nonempty f : ℝ) : ℂ) • φ ∧ ‖v - φ‖ ≤ δ := by
  intro n f δ hδ
  set m : ℝ := Finset.univ.sup' Finset.univ_nonempty f with hm
  have hfm : ∀ i, f i ≤ m := fun i => Finset.le_sup' f (Finset.mem_univ i)
  obtain ⟨zs, -, hzs⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  -- the gap `g` below the maximum
  set off := Finset.univ.filter (fun i => f i ≠ m) with hoff
  set g : ℝ := if h : off.Nonempty then m - off.sup' h f else 1 with hg
  have hgpos : 0 < g := by
    rw [hg]; split_ifs with h
    · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' h f
      have hj' : f j ≠ m := (Finset.mem_filter.mp hj).2
      have := hfm j
      rw [hjeq]; exact sub_pos.mpr (lt_of_le_of_ne this hj')
    · exact one_pos
  have hgle : ∀ i, f i ≠ m → g ≤ m - f i := by
    intro i hi
    have hmem : i ∈ off := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    rw [hg, dif_pos ⟨i, hmem⟩]
    have := Finset.le_sup' f hmem
    linarith
  set C : ℝ := ‖actCLM (qaoaMixer n)‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  set w0 : ℝ := min (δ ^ 2 / 4) (min (δ / 2) (1 / 2)) with hw0
  have hw0pos : 0 < w0 := by positivity
  set t : ℝ := min (1 / 2) (g * w0 / (4 * C + 1)) with ht
  have htpos : 0 < t := by positivity
  have ht2 : t ≤ 1 / 2 := min_le_left _ _
  have htg : t * (4 * C + 1) ≤ g * w0 := by
    have := min_le_right (1 / 2 : ℝ) (g * w0 / (4 * C + 1))
    rw [← ht] at this
    rwa [le_div_iff₀ (by positivity)] at this
  refine ⟨1 - t, ⟨by linarith, by linarith⟩, ?_⟩
  intro v hv μ heig hmin
  have hv1 : ‖v‖ = 1 := hv
  set H := linInterp (qaoaMixer n) (problemHamiltonian f) (1 - t) with hH
  -- Q(H, v) = -μ
  have hQv : Q H v = -μ := by
    have : Q (-H) v = μ := by
      simp only [Q, heig, inner_smul_right, inner_self_eq_norm_sq_to_K, hv1]
      simp
    rw [Q_neg] at this; linarith
  -- comparison with the basis vector at an argmax
  set e : EuclideanSpace ℂ (Qubits n) := EuclideanSpace.single zs 1 with he
  have he1 : ‖e‖ = 1 := by simp [he]
  have hQe : Q H e ≤ -μ := by
    have := hmin e
    rw [he1] at this
    have h2 : Q (-H) e = RCLike.re (inner ℂ e (act (-H) e)) := rfl
    rw [Q_neg] at h2; linarith
  have hQDe : Q (problemHamiltonian f) e = m := by
    unfold problemHamiltonian
    rw [Q_diag]
    rw [Finset.sum_eq_single zs (fun b _ hb => by simp [he, hb]) (by simp)]
    simp [he, hm, hzs]
  have hQDv : Q (problemHamiltonian f) v = ∑ i, f i * ‖v i‖ ^ 2 := by
    unfold problemHamiltonian; rw [Q_diag]
  have hsum1 : ∑ i, ‖v i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hv1, one_pow]
  have hIe := Q_abs_le (qaoaMixer n) e
  have hIv := Q_abs_le (qaoaMixer n) v
  rw [he1] at hIe; rw [hv1] at hIv
  rw [← hC] at hIe hIv
  have hLe := Q_lin (qaoaMixer n) (problemHamiltonian f) (1 - t) e
  have hLv := Q_lin (qaoaMixer n) (problemHamiltonian f) (1 - t) v
  rw [← hH] at hLe hLv
  -- the energy deficit
  set x : ℝ := m - ∑ i, f i * ‖v i‖ ^ 2 with hx
  have hx0 : 0 ≤ x := by
    have : ∑ i, f i * ‖v i‖ ^ 2 ≤ ∑ i, m * ‖v i‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hfm i) (by positivity)
    rw [← Finset.mul_sum, hsum1, mul_one] at this
    linarith
  have hxle : x ≤ g * w0 := by
    rw [abs_le] at hIe hIv
    have key : (1 - t) * x ≤ 2 * t * C := by
      rw [hx]; nlinarith [hIe.1, hIe.2, hIv.1, hIv.2]
    nlinarith
  -- weight off the argmax set
  set wt : ℝ := ∑ i, if f i = m then 0 else ‖v i‖ ^ 2 with hwt
  have hwt0 : 0 ≤ wt := Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
  have hgw : g * wt ≤ x := by
    have : x = ∑ i, (m - f i) * ‖v i‖ ^ 2 := by
      rw [hx]; simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum1, mul_one]
    rw [this, hwt, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with h
    · simp [h]
    · exact mul_le_mul_of_nonneg_right (hgle i h) (by positivity)
  have hwtw0 : wt ≤ w0 := by
    have := le_trans hgw hxle
    exact le_of_mul_le_mul_left this hgpos
  -- projection onto the argmax coordinates
  set P : EuclideanSpace ℂ (Qubits n) :=
    WithLp.toLp 2 (fun i => if f i = m then v i else 0) with hP
  have hPi : ∀ i, P i = if f i = m then v i else 0 := fun i => rfl
  have hPn : ‖P‖ ^ 2 = 1 - wt := by
    rw [EuclideanSpace.norm_sq_eq, ← hsum1, hwt, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hPi]; split_ifs <;> simp
  have hvPn : ‖v - P‖ ^ 2 = wt := by
    rw [EuclideanSpace.norm_sq_eq, hwt]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.sub_apply, hPi]; split_ifs <;> simp
  have hw0a : w0 ≤ δ ^ 2 / 4 := min_le_left _ _
  have hw0b : w0 ≤ δ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hw0c : w0 ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hPpos : 0 < ‖P‖ := by
    have : 0 < ‖P‖ ^ 2 := by rw [hPn]; linarith
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at this; simp at this)
  set φ : EuclideanSpace ℂ (Qubits n) := ((‖P‖⁻¹ : ℝ) : ℂ) • P with hφ
  clear_value φ P wt x w0 t g C
  refine ⟨φ, ?_, ?_, ?_⟩
  · show ‖φ‖ = 1
    rw [hφ, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hPpos.ne']
  · ext i
    simp only [problemHamiltonian, act, Matrix.mulVec_diagonal, WithLp.ofLp_toLp, hφ,
      PiLp.smul_apply, smul_eq_mul, hPi]
    split_ifs with h
    · rw [h]
    all_goals simp
  · have hd1 : ‖v - P‖ ≤ δ / 2 := by
      apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
      rw [hvPn]
      calc wt ≤ w0 := hwtw0
        _ ≤ δ ^ 2 / 4 := hw0a
        _ = (δ / 2) ^ 2 := by ring
    have hPle : ‖P‖ ≤ 1 := by
      by_contra hc
      replace hc := not_le.mp hc
      have := one_lt_pow₀ hc two_ne_zero
      linarith only [this, hPn, hwt0]
    have hd2 : ‖P - φ‖ = 1 - ‖P‖ := by
      have : P - φ = ((1 - ‖P‖⁻¹ : ℝ) : ℂ) • P := by
        rw [hφ, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
      rw [this, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have hinv : 1 ≤ ‖P‖⁻¹ := one_le_inv₀ hPpos |>.mpr hPle
      rw [abs_of_nonpos (by linarith only [hinv]), neg_sub, sub_mul, inv_mul_cancel₀ hPpos.ne', one_mul]
    have hd3 : 1 - ‖P‖ ≤ δ / 2 := by
      have hsq : ‖P‖ ^ 2 ≤ ‖P‖ := by
        rw [sq]; exact mul_le_of_le_one_left (norm_nonneg _) hPle
      linarith only [hPn, hwtw0, hw0b, hsq]
    calc ‖v - φ‖ = ‖(v - P) + (P - φ)‖ := by congr 1; abel
      _ ≤ ‖v - P‖ + ‖P - φ‖ := norm_add_le _ _
      _ ≤ δ := by rw [hd2]; linarith only [hd1, hd3]

end C2Sec

section C3Sec

/-! C3 for 52c231a1: global existence for the linear adiabatic ODE (Picard–Lindelöf on short
intervals, glued). -/

open QAlgorithms Set Metric
open scoped NNReal

namespace C3Aux

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [CompleteSpace E]

lemma short (G : ℝ → E →L[ℂ] E) (K : ℝ) (hK : 0 ≤ K)
    (t0 h : ℝ) (hh : 0 ≤ h) (hKh : K * h ≤ 1 / 2)
    (hG : ContinuousOn G (Icc t0 (t0 + h))) (hGK : ∀ t ∈ Icc t0 (t0 + h), ‖G t‖ ≤ K) (x : E) :
    ∃ α : ℝ → E, α t0 = x ∧ ∀ t ∈ Icc t0 (t0 + h),
      HasDerivWithinAt α (G t (α t)) (Icc t0 (t0 + h)) t := by
  have ht0 : t0 ∈ Icc t0 (t0 + h) := ⟨le_rfl, by linarith⟩
  have hPL : IsPicardLindelof (fun t y => G t y) (tmin := t0) (tmax := t0 + h) ⟨t0, ht0⟩ x
      ⟨‖x‖ + 1, by positivity⟩ 0 ⟨K * (2 * ‖x‖ + 1), by positivity⟩ ⟨K, hK⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      refine LipschitzWith.lipschitzOnWith ?_
      refine LipschitzWith.of_dist_le_mul fun y z => ?_
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact (G t).le_of_opNorm_le (hGK t ht) _
    · intro y _
      exact ((ContinuousLinearMap.apply ℂ E y).continuous).comp_continuousOn hG
    · intro t ht y hy
      have hy1 : ‖y - x‖ ≤ ‖x‖ + 1 := by
        have := mem_closedBall_iff_norm.mp hy
        exact this
      have hy' : ‖y‖ ≤ 2 * ‖x‖ + 1 := by
        have := norm_le_norm_sub_add y x
        linarith
      show ‖G t y‖ ≤ K * (2 * ‖x‖ + 1)
      calc ‖G t y‖ ≤ K * ‖y‖ := (G t).le_of_opNorm_le (hGK t ht) _
        _ ≤ K * (2 * ‖x‖ + 1) := by gcongr
    · have hm : max (t0 + h - t0) (t0 - t0) = h := by
        rw [add_sub_cancel_left, sub_self]; exact max_eq_left hh
      show K * (2 * ‖x‖ + 1) * max (t0 + h - t0) (t0 - t0) ≤ (‖x‖ + 1) - 0
      rw [hm]
      have := mul_le_mul_of_nonneg_left hKh (by positivity : (0:ℝ) ≤ 2 * ‖x‖ + 1)
      nlinarith [norm_nonneg x]
  obtain ⟨α, h0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h0, hα⟩

lemma glue_step (G : ℝ → E →L[ℂ] E) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (α β : ℝ → E)
    (hαβ : α b = β b)
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (G t (α t)) (Icc a b) t)
    (hβ : ∀ t ∈ Icc b c, HasDerivWithinAt β (G t (β t)) (Icc b c) t) :
    ∀ t ∈ Icc a c, HasDerivWithinAt (fun s => if s ≤ b then α s else β s)
      (G t (if t ≤ b then α t else β t)) (Icc a c) t := by
  intro t _
  have hu : Icc a c = Icc a b ∪ Icc b c := (Icc_union_Icc_eq_Icc hab hbc).symm
  rw [hu]
  have hγα : ∀ s ∈ Icc a b, (fun s => if s ≤ b then α s else β s) s = α s :=
    fun s hs => if_pos hs.2
  have hγβ : ∀ s ∈ Icc b c, (fun s => if s ≤ b then α s else β s) s = β s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst h; simp [hαβ]
    · simp [not_le.mpr h]
  apply HasDerivWithinAt.union
  · by_cases h : t ∈ Icc a b
    · have := (hα t h).congr hγα (hγα t h)
      have e : (if t ≤ b then α t else β t) = α t := hγα t h
      rw [e]; exact this
    · exact HasFDerivWithinAt.of_notMem_closure (by rw [isClosed_Icc.closure_eq]; exact h)
  · by_cases h : t ∈ Icc b c
    · have := (hβ t h).congr hγβ (hγβ t h)
      have e : (if t ≤ b then α t else β t) = β t := hγβ t h
      rw [e]; exact this
    · exact HasFDerivWithinAt.of_notMem_closure (by rw [isClosed_Icc.closure_eq]; exact h)

lemma global (G : ℝ → E →L[ℂ] E) (K : ℝ) (hK : 0 ≤ K) (hG : ContinuousOn G (Icc 0 1))
    (hGK : ∀ t ∈ Icc (0:ℝ) 1, ‖G t‖ ≤ K) (x : E) :
    ∃ α : ℝ → E, α 0 = x ∧
      ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt α (G t (α t)) (Icc 0 1) t := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * K)
  have hNpos : (0:ℝ) < N := by linarith
  set h : ℝ := 1 / N with hhdef
  have hh : 0 ≤ h := by positivity
  have hKh : K * h ≤ 1 / 2 := by
    rw [hhdef, mul_one_div, div_le_iff₀ hNpos]; linarith
  have hNh : (N : ℝ) * h = 1 := by rw [hhdef]; field_simp
  have key : ∀ k : ℕ, k + 1 ≤ N → ∃ α : ℝ → E, α 0 = x ∧
      ∀ t ∈ Icc (0:ℝ) ((k + 1 : ℕ) * h),
        HasDerivWithinAt α (G t (α t)) (Icc 0 ((k + 1 : ℕ) * h)) t := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hsub : Icc (0:ℝ) (0 + h) ⊆ Icc 0 1 := by
        apply Icc_subset_Icc le_rfl
        have : (1:ℝ) ≤ N := by exact_mod_cast hk
        rw [zero_add, ← hNh]; nlinarith
      obtain ⟨α, h0, hα⟩ := short G K hK 0 h hh hKh (hG.mono hsub)
        (fun t ht => hGK t (hsub ht)) x
      refine ⟨α, h0, ?_⟩
      have : ((0 + 1 : ℕ) : ℝ) * h = 0 + h := by simp
      rw [this]; exact hα
    | succ k ih =>
      intro hk
      obtain ⟨α, h0, hα⟩ := ih (by omega)
      set b : ℝ := ((k + 1 : ℕ) : ℝ) * h with hb
      have hb0 : 0 ≤ b := by positivity
      have hbc : ((k + 1 + 1 : ℕ) : ℝ) * h = b + h := by rw [hb]; push_cast; ring
      have hsub : Icc b (b + h) ⊆ Icc 0 1 := by
        apply Icc_subset_Icc hb0
        rw [← hbc, ← hNh]
        have : ((k + 1 + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
        nlinarith
      obtain ⟨β, hβ0, hβ⟩ := short G K hK b h hh hKh (hG.mono hsub)
        (fun t ht => hGK t (hsub ht)) (α b)
      refine ⟨fun s => if s ≤ b then α s else β s, by simp [hb0, h0], ?_⟩
      rw [hbc]
      exact glue_step G 0 b (b + h) hb0 (by linarith) α β hβ0.symm hα hβ
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by
    have : 0 < N := by exact_mod_cast hNpos
    omega⟩
  obtain ⟨α, h0, hα⟩ := key M le_rfl
  rw [hNh] at hα
  exact ⟨α, h0, hα⟩

/-- `act A` as a continuous ℂ-linear map. -/
noncomputable def actCLM {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := act A
      map_add' := fun x y => by simp [act, Matrix.mulVec_add]
      map_smul' := fun c x => by simp [act, Matrix.mulVec_smul] }

lemma actCLM_apply {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    actCLM A x = act A x := rfl

end C3Aux

open C3Aux in
theorem c3_solution :
    ∀ {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) (T : ℝ) (x : EuclideanSpace ℂ ι),
      ∃ ψ : ℝ → EuclideanSpace ℂ ι, SolvesAdiabaticPlus (linInterp A B) T ψ ∧ ψ 0 = x := by
  intro ι _ A B T x
  set G : ℝ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι := fun s =>
    (Complex.I * (T : ℂ)) • ((((1 - s : ℝ)) : ℂ) • actCLM A + (s : ℂ) • actCLM B) with hGdef
  have hF : ∀ s v, G s v = Complex.I • (T : ℂ) • act (linInterp A B s) v := by
    intro s v
    simp only [hGdef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      actCLM_apply, linInterp, act, Matrix.add_mulVec, Matrix.smul_mulVec, smul_smul]
    simp [smul_add, smul_smul, Matrix.smul_mulVec, WithLp.toLp_smul]
  have hG : Continuous G := by
    rw [hGdef]; fun_prop
  set K : ℝ := ‖Complex.I * (T : ℂ)‖ * (‖actCLM A‖ + ‖actCLM B‖) with hK
  have hK0 : 0 ≤ K := by positivity
  have hGK : ∀ t ∈ Icc (0:ℝ) 1, ‖G t‖ ≤ K := by
    intro t ht
    rw [hGdef, hK]
    simp only
    rw [norm_smul]
    gcongr
    calc ‖(((1 - t : ℝ)) : ℂ) • actCLM A + (t : ℂ) • actCLM B‖
        ≤ ‖(((1 - t : ℝ)) : ℂ) • actCLM A‖ + ‖(t : ℂ) • actCLM B‖ := norm_add_le _ _
      _ = |1 - t| * ‖actCLM A‖ + |t| * ‖actCLM B‖ := by
          rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ 1 * ‖actCLM A‖ + 1 * ‖actCLM B‖ := by
          gcongr
          · rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
          · rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      _ = ‖actCLM A‖ + ‖actCLM B‖ := by ring
  obtain ⟨α, h0, hα⟩ := global G K hK0 hG.continuousOn hGK x
  refine ⟨α, fun s hs => ?_, h0⟩
  rw [← hF]
  exact hα s hs

end C3Sec

section C4Sec

open QAlgorithms

namespace QAOAC4

open scoped Matrix.Norms.L2Operator

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma act_mul (M N : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (M * N) v = act M (act N v) := by
  simp [act, Matrix.mulVec_mulVec]

lemma act_one (v : EuclideanSpace ℂ ι) : act (1 : Matrix ι ι ℂ) v = v := by
  simp [act]

lemma act_sub_vec (M : Matrix ι ι ℂ) (v w : EuclideanSpace ℂ ι) :
    act M (v - w) = act M v - act M w := by
  simp [act, Matrix.mulVec_sub]

lemma act_sub_mat (M N : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (M - N) v = act M v - act N v := by
  simp [act, Matrix.sub_mulVec]

lemma act_add_mat (M N : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (M + N) v = act M v + act N v := by
  simp [act, Matrix.add_mulVec]

lemma norm_act_le (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : ‖act A v‖ ≤ ‖A‖ * ‖v‖ := by
  have := Matrix.l2_opNorm_mulVec A v
  simpa [act, EuclideanSpace.equiv] using this

lemma skew_mem (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℝ) :
    (-(Complex.I * (r : ℂ))) • A ∈ skewAdjoint (Matrix ι ι ℂ) := by
  have hs : star (-(Complex.I * (r : ℂ))) = Complex.I * (r : ℂ) := by
    simp [Complex.conj_ofReal]
  have hA' : star A = A := hA
  rw [skewAdjoint.mem_iff, star_smul, hs, hA', neg_smul, neg_neg]

lemma norm_exp_skew_le (X : Matrix ι ι ℂ) (hX : X ∈ skewAdjoint (Matrix ι ι ℂ)) :
    ‖NormedSpace.exp X‖ ≤ 1 := by
  have hstar : star (NormedSpace.exp X) = NormedSpace.exp (-X) := by
    rw [← skewAdjoint.mem_iff.mp hX, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
    rw [Matrix.exp_conjTranspose]
  have hU : NormedSpace.exp X ∈ unitary (Matrix ι ι ℂ) := by
    rw [Unitary.mem_iff, hstar, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_right, neg_add_cancel, add_neg_cancel,
      NormedSpace.exp_zero]
    exact ⟨rfl, rfl⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : NormedSpace.exp X = 0 := Subsingleton.elim _ _
    rw [this, norm_zero]; norm_num
  · rw [CStarRing.norm_of_mem_unitary hU]

lemma skew_real_smul (X : Matrix ι ι ℂ) (hX : X ∈ skewAdjoint (Matrix ι ι ℂ)) (τ : ℝ) :
    (τ : ℂ) • X ∈ skewAdjoint (Matrix ι ι ℂ) := by
  rw [skewAdjoint.mem_iff] at hX ⊢
  rw [star_smul, hX, Complex.star_def, Complex.conj_ofReal, smul_neg]

/-- first-order Taylor bound from a derivative modulus. -/
lemma taylor1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g g' : ℝ → E)
    (a b K : ℝ) (hab : a ≤ b)
    (hg : ∀ x ∈ Set.Icc a b, HasDerivWithinAt g (g' x) (Set.Icc a b) x)
    (hK : ∀ x ∈ Set.Icc a b, ‖g' x - g' a‖ ≤ K) :
    ‖g b - g a - (b - a) • g' a‖ ≤ K * (b - a) := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun x => g x - (x - a) • g' a) (f' := fun x => g' x - g' a) (C := K)
    (fun x hx => by
      have h2 := ((hasDerivWithinAt_id x (Set.Icc a b)).sub_const a).smul_const (g' a)
      have h3 := (hg x hx).sub h2
      rw [one_smul] at h3
      exact h3)
    (fun x hx => hK x (Set.Ico_subset_Icc_self hx)) b ⟨hab, le_rfl⟩
  simp only [sub_self, zero_smul, sub_zero] at key
  convert key using 2
  abel

/-- one Trotter step, local error, in any complete normed `ℂ`-algebra with contractive flows. -/
lemma trotter_local_gen {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (X Y : 𝔸) (hXn : ∀ τ : ℝ, ‖NormedSpace.exp ((τ : ℂ) • X)‖ ≤ 1)
    (hYn : ∀ τ : ℝ, ‖NormedSpace.exp ((τ : ℂ) • Y)‖ ≤ 1) :
    ‖NormedSpace.exp X * NormedSpace.exp Y - 1 - (X + Y)‖ ≤ (‖X‖ + ‖Y‖) ^ 2 := by
  set f : ℝ → 𝔸 := fun τ =>
    NormedSpace.exp ((τ : ℂ) • X) * NormedSpace.exp ((τ : ℂ) • Y) with hf
  have hder : ∀ τ : ℝ, HasDerivAt f (X * f τ + f τ * Y) τ := by
    intro τ
    have h1 := HasDerivAt.scomp (x := τ) (h := Complex.ofRealCLM)
      (hasDerivAt_exp_smul_const' X (τ : ℂ)) (Complex.ofRealCLM.hasDerivAt)
    have h2 := HasDerivAt.scomp (x := τ) (h := Complex.ofRealCLM)
      (hasDerivAt_exp_smul_const Y (τ : ℂ)) (Complex.ofRealCLM.hasDerivAt)
    have h3 := h1.mul h2
    simp only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at h3
    convert h3 using 1
    all_goals first
      | rfl
      | ((try simp only [hf]); noncomm_ring)
  have hfn : ∀ τ : ℝ, ‖f τ‖ ≤ 1 := by
    intro τ
    calc ‖f τ‖ ≤ ‖NormedSpace.exp ((τ : ℂ) • X)‖ * ‖NormedSpace.exp ((τ : ℂ) • Y)‖ :=
          norm_mul_le _ _
      _ ≤ 1 * 1 := by
          gcongr
          · exact hXn τ
          · exact hYn τ
      _ = 1 := by norm_num
  have hf0 : f 0 = 1 := by simp [hf]
  have hf1 : f 1 = NormedSpace.exp X * NormedSpace.exp Y := by simp [hf]
  have hmv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖f τ - f 0‖ ≤ (‖X‖ + ‖Y‖) * (τ - 0) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment'
      (fun x _ => (hder x).hasDerivWithinAt) (fun x _ => ?_)
    calc ‖X * f x + f x * Y‖ ≤ ‖X‖ * ‖f x‖ + ‖f x‖ * ‖Y‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ‖X‖ * 1 + 1 * ‖Y‖ := by
          gcongr
          · exact hfn x
          · exact hfn x
      _ = ‖X‖ + ‖Y‖ := by ring
  have hK : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(X * f τ + f τ * Y) - (X * f 0 + f 0 * Y)‖ ≤ (‖X‖ + ‖Y‖) ^ 2 := by
    intro τ hτ
    have hd : (X * f τ + f τ * Y) - (X * f 0 + f 0 * Y) =
        X * (f τ - f 0) + (f τ - f 0) * Y := by noncomm_ring
    rw [hd]
    have hm := hmv τ hτ
    have hτ1 : (‖X‖ + ‖Y‖) * (τ - 0) ≤ ‖X‖ + ‖Y‖ := by
      have : 0 ≤ ‖X‖ + ‖Y‖ := by positivity
      nlinarith [hτ.2, hτ.1]
    calc ‖X * (f τ - f 0) + (f τ - f 0) * Y‖
        ≤ ‖X‖ * ‖f τ - f 0‖ + ‖f τ - f 0‖ * ‖Y‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ‖X‖ * (‖X‖ + ‖Y‖) + (‖X‖ + ‖Y‖) * ‖Y‖ := by
          gcongr <;> exact hm.trans hτ1
      _ = (‖X‖ + ‖Y‖) ^ 2 := by ring
  have ht := taylor1 f (fun τ => X * f τ + f τ * Y) 0 1 ((‖X‖ + ‖Y‖) ^ 2) zero_le_one
    (fun x _ => (hder x).hasDerivWithinAt) hK
  rw [hf1, hf0] at ht
  simpa using ht

/-- one Trotter step, local error (skew-adjoint matrix generators, L2 operator norm). -/
lemma trotter_local (X Y : Matrix ι ι ℂ) (hX : X ∈ skewAdjoint (Matrix ι ι ℂ))
    (hY : Y ∈ skewAdjoint (Matrix ι ι ℂ)) :
    ‖NormedSpace.exp X * NormedSpace.exp Y - 1 - (X + Y)‖ ≤ (‖X‖ + ‖Y‖) ^ 2 :=
  trotter_local_gen X Y (fun τ => norm_exp_skew_le _ (skew_real_smul X hX τ))
    (fun τ => norm_exp_skew_le _ (skew_real_smul Y hY τ))

/-- Lady Windermere's fan: contractive steps, per-step error `e`. -/
lemma telescope (p : ℕ) (U : Fin p → Matrix ι ι ℂ) (hU : ∀ k, ‖U k‖ ≤ 1)
    (x : ℕ → EuclideanSpace ℂ ι) (e : ℝ)
    (hx : ∀ k : Fin p, ‖act (U k) (x k) - x (k + 1)‖ ≤ e) :
    ‖act (orderedProd U) (x 0) - x p‖ ≤ p * e := by
  induction p with
  | zero => simp [orderedProd, act_one]
  | succ p ih =>
    have hprod : orderedProd U =
        U (Fin.last p) * orderedProd (fun k : Fin p => U k.castSucc) := by
      rw [orderedProd, orderedProd, List.ofFn_succ', List.concat_eq_append, List.reverse_append]
      simp
    rw [hprod, act_mul]
    have h1 := ih (fun k => U k.castSucc) (fun k => hU _) (fun k => by simpa using hx k.castSucc)
    have h2 := hx (Fin.last p)
    simp only [Fin.val_last] at h2
    set w := act (orderedProd (fun k : Fin p => U k.castSucc)) (x 0)
    have hsplit : act (U (Fin.last p)) w - x (p + 1) =
        act (U (Fin.last p)) (w - x p) + (act (U (Fin.last p)) (x p) - x (p + 1)) := by
      rw [act_sub_vec]; abel
    rw [hsplit]
    calc ‖act (U (Fin.last p)) (w - x p) + (act (U (Fin.last p)) (x p) - x (p + 1))‖
        ≤ ‖U (Fin.last p)‖ * ‖w - x p‖ + e :=
          (norm_add_le _ _).trans (add_le_add (norm_act_le _ _) h2)
      _ ≤ 1 * (p * e) + e := by
          gcongr
          · exact hU _
      _ = ((p + 1 : ℕ) : ℝ) * e := by push_cast; ring

lemma linInterp_sub (A B : Matrix ι ι ℂ) (s t : ℝ) :
    linInterp A B s - linInterp A B t = ((t - s : ℝ) : ℂ) • A + ((s - t : ℝ) : ℂ) • B := by
  ext i j
  simp only [linInterp, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast; ring

lemma norm_cs (r : ℝ) (A : Matrix ι ι ℂ) : ‖(r : ℂ) • A‖ = |r| * ‖A‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- local consistency of the adiabatic ODE solution (second-order remainder). -/
lemma ode_local (A B : Matrix ι ι ℂ) (T : ℝ) (ψ : ℝ → EuclideanSpace ℂ ι)
    (hψ : SolvesAdiabaticPlus (linInterp A B) T ψ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t h : ℝ, 0 ≤ t → 0 ≤ h → t + h ≤ 1 →
      ‖ψ (t + h) - ψ t - h • (Complex.I • (T : ℂ) • act (linInterp A B t) (ψ t))‖ ≤
        L * h ^ 2 := by
  set D : ℝ → EuclideanSpace ℂ ι :=
    fun s => Complex.I • (T : ℂ) • act (linInterp A B s) (ψ s) with hD
  have hcont : ContinuousOn ψ (Set.Icc 0 1) := fun s hs => (hψ s hs).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  set NA := ‖A‖ + ‖B‖ with hNA
  have hNA0 : 0 ≤ NA := by positivity
  have hH : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖linInterp A B s‖ ≤ NA := by
    intro s hs
    unfold linInterp
    calc ‖((1 - s : ℝ) : ℂ) • A + (s : ℂ) • B‖ ≤ ‖((1 - s : ℝ) : ℂ) • A‖ + ‖(s : ℂ) • B‖ :=
          norm_add_le _ _
      _ = |1 - s| * ‖A‖ + |s| * ‖B‖ := by rw [norm_cs, norm_cs]
      _ ≤ 1 * ‖A‖ + 1 * ‖B‖ := by
          gcongr
          · rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
          · rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
      _ = NA := by ring
  have hHd : ∀ s t : ℝ, ‖linInterp A B s - linInterp A B t‖ ≤ |s - t| * NA := by
    intro s t
    rw [linInterp_sub]
    calc _ ≤ ‖((t - s : ℝ) : ℂ) • A‖ + ‖((s - t : ℝ) : ℂ) • B‖ := norm_add_le _ _
      _ = |s - t| * NA := by rw [norm_cs, norm_cs, abs_sub_comm t s]; ring
  set M1 := |T| * NA * M with hM1
  have hM10 : 0 ≤ M1 := mul_nonneg (mul_nonneg (abs_nonneg _) hNA0) hM0
  have hDb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖D s‖ ≤ M1 := by
    intro s hs
    simp only [hD]
    rw [norm_smul, norm_smul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    calc |T| * ‖act (linInterp A B s) (ψ s)‖ ≤ |T| * (NA * M) := by
          gcongr
          exact (norm_act_le _ _).trans (mul_le_mul (hH s hs) (hM s hs) (norm_nonneg _) hNA0)
      _ = M1 := by rw [hM1]; ring
  have hLip : ∀ t s : ℝ, 0 ≤ t → t ≤ s → s ≤ 1 → ‖ψ s - ψ t‖ ≤ M1 * (s - t) := by
    intro t s ht hts hs1
    exact norm_image_sub_le_of_norm_deriv_le_segment' (f := ψ) (f' := D) (a := t) (b := 1)
      (C := M1)
      (fun x hx => (hψ x ⟨ht.trans hx.1, hx.2⟩).mono (Set.Icc_subset_Icc ht le_rfl))
      (fun x hx => hDb x ⟨ht.trans hx.1, hx.2.le⟩) s ⟨hts, hs1⟩
  set L := |T| * NA * (M + M1) with hLdef
  have hL0 : 0 ≤ L := mul_nonneg (mul_nonneg (abs_nonneg _) hNA0) (by linarith)
  have hDL : ∀ t s : ℝ, 0 ≤ t → t ≤ s → s ≤ 1 → ‖D s - D t‖ ≤ L * (s - t) := by
    intro t s ht hts hs1
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.trans hts, hs1⟩
    have htt : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, hts.trans hs1⟩
    have e : D s - D t = Complex.I • (T : ℂ) • (act (linInterp A B s - linInterp A B t) (ψ s) +
        act (linInterp A B t) (ψ s - ψ t)) := by
      rw [act_sub_mat, act_sub_vec]
      simp only [hD, smul_sub, smul_add]
      abel
    rw [e, norm_smul, norm_smul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    have h1 : ‖act (linInterp A B s - linInterp A B t) (ψ s)‖ ≤ (s - t) * NA * M := by
      refine (norm_act_le _ _).trans ?_
      have := hHd s t
      rw [abs_of_nonneg (by linarith)] at this
      exact mul_le_mul this (hM s hs) (norm_nonneg _)
        (mul_nonneg (by linarith) hNA0)
    have h2 : ‖act (linInterp A B t) (ψ s - ψ t)‖ ≤ NA * (M1 * (s - t)) :=
      (norm_act_le _ _).trans
        (mul_le_mul (hH t htt) (hLip t s ht hts hs1) (norm_nonneg _) hNA0)
    calc |T| * ‖act (linInterp A B s - linInterp A B t) (ψ s) +
          act (linInterp A B t) (ψ s - ψ t)‖
        ≤ |T| * ((s - t) * NA * M + NA * (M1 * (s - t))) := by
          gcongr; exact (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = L * (s - t) := by rw [hLdef, hM1]; ring
  refine ⟨L, hL0, fun t h ht hh hth => ?_⟩
  have hint := taylor1 ψ D t (t + h) (L * h) (by linarith)
    (fun x hx => (hψ x ⟨ht.trans hx.1, hx.2.trans hth⟩).mono (Set.Icc_subset_Icc ht hth))
    (fun x hx => (hDL t x ht hx.1 (hx.2.trans hth)).trans
      (mul_le_mul_of_nonneg_left (by linarith [hx.2]) hL0))
  have e2 : t + h - t = h := by ring
  rw [e2] at hint
  calc ‖ψ (t + h) - ψ t - h • D t‖ ≤ L * h * h := hint
    _ = L * h ^ 2 := by ring

lemma act_smul_mat (c : ℂ) (M : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (c • M) v = c • act M v := by
  ext i
  simp [act, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

lemma gen_eq (HI HF : Matrix ι ι ℂ) (s0 t h T : ℝ) :
    -(Complex.I * ((h * T * (1 - t * s0) : ℝ) : ℂ)) • HI +
        -(Complex.I * ((h * T * (t * s0) : ℝ) : ℂ)) • HF =
      ((h : ℂ) * (Complex.I * (T : ℂ))) • linInterp (-HI) (-linInterp HI HF s0) t := by
  ext i j
  simp only [linInterp, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  push_cast; ring

/-- C4 for general Hermitian `H_I, H_F`: first-order time-dependent Trotterisation. -/
theorem c4_gen (HI HF : Matrix ι ι ℂ) (hI : HI.IsHermitian) (hF : HF.IsHermitian)
    (s0 T : ℝ) (hs0 : s0 ∈ Set.Icc (0 : ℝ) 1) (hT : 0 ≤ T) (ψ : ℝ → EuclideanSpace ℂ ι)
    (hψ : SolvesAdiabaticPlus (linInterp (-HI) (-linInterp HI HF s0)) T ψ)
    (ε : ℝ) (hε : 0 < ε) : ∃ P : ℕ, 1 ≤ P ∧ ∀ p : ℕ, P ≤ p →
      ∃ β θ : Fin p → ℝ, (∀ k, β k ∈ Set.Icc 0 (2 * Real.pi)) ∧
        (∀ k, θ k ∈ Set.Icc 0 (2 * Real.pi)) ∧
        ‖act (orderedProd fun k : Fin p =>
            NormedSpace.exp (-(Complex.I * (β k : ℂ)) • HI) *
              NormedSpace.exp (-(Complex.I * (θ k : ℂ)) • HF)) (ψ 0) - ψ 1‖ ≤ ε := by
  obtain ⟨L, hL0, hL⟩ := ode_local (-HI) (-linInterp HI HF s0) T ψ hψ
  have hcont : ContinuousOn ψ (Set.Icc 0 1) := fun s hs => (hψ s hs).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  set N := ‖HI‖ + ‖HF‖ with hN
  have hN0 : 0 ≤ N := by positivity
  set C := (T * N) ^ 2 * M + L with hC
  have hC0 : 0 ≤ C := by positivity
  obtain ⟨P, hP⟩ := exists_nat_ge (max (C / ε) (T / (2 * Real.pi)))
  refine ⟨P + 1, by omega, fun p hp => ?_⟩
  have hpP : (P : ℝ) + 1 ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith [(Nat.cast_nonneg P : (0 : ℝ) ≤ P)]
  set h : ℝ := 1 / p with hh
  have hh0 : 0 < h := by positivity
  have hpi : 0 < 2 * Real.pi := by positivity
  have hhT : h * T ≤ 2 * Real.pi := by
    have h1 : T / (2 * Real.pi) ≤ p := by
      linarith [le_max_right (C / ε) (T / (2 * Real.pi))]
    rw [div_le_iff₀ hpi] at h1
    rw [hh, div_mul_eq_mul_div, one_mul, div_le_iff₀ hp0]
    linarith
  set tk : Fin p → ℝ := fun k => ((k : ℕ) : ℝ) / p with htk
  have htk0 : ∀ k : Fin p, 0 ≤ tk k := fun k => by positivity
  have htk1 : ∀ k : Fin p, tk k + h ≤ 1 := by
    intro k
    have hk : ((k : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast k.isLt
    simp only [htk, hh]
    rw [← add_div, div_le_one hp0]; exact hk
  have hts : ∀ k : Fin p, 0 ≤ tk k * s0 ∧ tk k * s0 ≤ 1 := by
    intro k
    have h1 : tk k ≤ 1 := by linarith [htk1 k]
    exact ⟨mul_nonneg (htk0 k) hs0.1, by nlinarith [htk0 k, hs0.1, hs0.2]⟩
  set β : Fin p → ℝ := fun k => h * T * (1 - tk k * s0) with hβ
  set θ : Fin p → ℝ := fun k => h * T * (tk k * s0) with hθ
  have hhT0 : 0 ≤ h * T := mul_nonneg hh0.le hT
  have hβb : ∀ k, 0 ≤ β k ∧ β k ≤ h * T := fun k => by
    constructor
    · exact mul_nonneg hhT0 (by linarith [(hts k).2])
    · have := (hts k).1
      simp only [hβ]; nlinarith
  have hθb : ∀ k, 0 ≤ θ k ∧ θ k ≤ h * T := fun k => by
    constructor
    · exact mul_nonneg hhT0 (hts k).1
    · have := (hts k).2
      simp only [hθ]; nlinarith
  refine ⟨β, θ, fun k => ⟨(hβb k).1, (hβb k).2.trans hhT⟩,
    fun k => ⟨(hθb k).1, (hθb k).2.trans hhT⟩, ?_⟩
  set U : Fin p → Matrix ι ι ℂ := fun k =>
    NormedSpace.exp (-(Complex.I * (β k : ℂ)) • HI) *
      NormedSpace.exp (-(Complex.I * (θ k : ℂ)) • HF) with hU
  have hUn : ∀ k, ‖U k‖ ≤ 1 := by
    intro k
    calc ‖U k‖ ≤ ‖NormedSpace.exp (-(Complex.I * (β k : ℂ)) • HI)‖ *
          ‖NormedSpace.exp (-(Complex.I * (θ k : ℂ)) • HF)‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := by
          gcongr
          · exact norm_exp_skew_le _ (skew_mem HI hI _)
          · exact norm_exp_skew_le _ (skew_mem HF hF _)
      _ = 1 := by norm_num
  set x : ℕ → EuclideanSpace ℂ ι := fun j => ψ (((j : ℕ) : ℝ) / p) with hx
  have hstep : ∀ k : Fin p, ‖act (U k) (x k) - x (k + 1)‖ ≤ C * h ^ 2 := by
    intro k
    have hxk : x k = ψ (tk k) := rfl
    have hxk1 : x (k + 1) = ψ (tk k + h) := by
      simp only [hx, htk, hh]; congr 1; push_cast; rw [add_div]
    rw [hxk, hxk1]
    set w := ψ (tk k)
    have hwM : ‖w‖ ≤ M := hM _ ⟨htk0 k, by linarith [htk1 k]⟩
    set X : Matrix ι ι ℂ := -(Complex.I * (β k : ℂ)) • HI with hX
    set Y : Matrix ι ι ℂ := -(Complex.I * (θ k : ℂ)) • HF with hY
    have hXn : ‖X‖ ≤ h * T * ‖HI‖ := by
      rw [hX, norm_smul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hβb k).1]
      exact mul_le_mul_of_nonneg_right (hβb k).2 (norm_nonneg _)
    have hYn : ‖Y‖ ≤ h * T * ‖HF‖ := by
      rw [hY, norm_smul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hθb k).1]
      exact mul_le_mul_of_nonneg_right (hθb k).2 (norm_nonneg _)
    have hXY : ‖X‖ + ‖Y‖ ≤ h * T * N := by rw [hN]; linarith
    have htl := trotter_local X Y (skew_mem HI hI _) (skew_mem HF hF _)
    have hlin : act (X + Y) w =
        h • (Complex.I • (T : ℂ) • act (linInterp (-HI) (-linInterp HI HF s0) (tk k)) w) := by
      have hg := gen_eq HI HF s0 (tk k) h T
      have e1 : X + Y = -(Complex.I * ((h * T * (1 - tk k * s0) : ℝ) : ℂ)) • HI +
          -(Complex.I * ((h * T * (tk k * s0) : ℝ) : ℂ)) • HF := rfl
      rw [e1, hg, act_smul_mat]
      ext i
      simp [Complex.real_smul]
      try ring
    have hsplit : act (U k) w - ψ (tk k + h) =
        act (U k - 1 - (X + Y)) w + -(ψ (tk k + h) - ψ (tk k) - act (X + Y) w) := by
      rw [act_sub_mat, act_sub_mat, act_one]; abel
    rw [hsplit]
    have hA : ‖act (U k - 1 - (X + Y)) w‖ ≤ (T * N) ^ 2 * M * h ^ 2 := by
      refine (norm_act_le _ _).trans ?_
      have hsq : (‖X‖ + ‖Y‖) ^ 2 ≤ (h * T * N) ^ 2 := by
        gcongr
      calc ‖U k - 1 - (X + Y)‖ * ‖w‖ ≤ (h * T * N) ^ 2 * M :=
            mul_le_mul (htl.trans hsq) hwM (norm_nonneg _) (by positivity)
        _ = (T * N) ^ 2 * M * h ^ 2 := by ring
    have hB : ‖-(ψ (tk k + h) - ψ (tk k) - act (X + Y) w)‖ ≤ L * h ^ 2 := by
      rw [norm_neg, hlin]
      exact hL (tk k) h (htk0 k) hh0.le (htk1 k)
    calc _ ≤ (T * N) ^ 2 * M * h ^ 2 + L * h ^ 2 := (norm_add_le _ _).trans (add_le_add hA hB)
      _ = C * h ^ 2 := by rw [hC]; ring
  have htel := telescope p U hUn x (C * h ^ 2) hstep
  have hx0 : x 0 = ψ 0 := by simp [hx]
  have hxp : x p = ψ 1 := by simp only [hx]; rw [div_self hp0.ne']
  rw [hx0, hxp] at htel
  refine htel.trans ?_
  have hCe : C / ε ≤ p := by linarith [le_max_left (C / ε) (T / (2 * Real.pi))]
  rw [div_le_iff₀ hε] at hCe
  rw [hh]
  have : (p : ℝ) * (C * (1 / (p : ℝ)) ^ 2) = C / p := by field_simp
  rw [this, div_le_iff₀ hp0]
  linarith

end QAOAC4

/-- C4 (Nannicini p.230, proof of Prop. 9.28): the adiabatic evolution along the negated path
`s ↦ -((1-s) H_I + s H(s0))` is approximated by alternating layers `e^{-iβ H_I} e^{-iθ H_F}` with
angles in `[0, 2π]`, for every large enough depth `p`. -/
theorem c4_solution :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (HI HF : Matrix ι ι ℂ), HI.IsHermitian →
      HF.IsHermitian → ∀ (s0 T : ℝ), s0 ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ T →
      ∀ ψ : ℝ → EuclideanSpace ℂ ι,
        SolvesAdiabaticPlus (linInterp (-HI) (-linInterp HI HF s0)) T ψ →
        ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, 1 ≤ P ∧ ∀ p : ℕ, P ≤ p →
          ∃ β θ : Fin p → ℝ, (∀ k, β k ∈ Set.Icc 0 (2 * Real.pi)) ∧
            (∀ k, θ k ∈ Set.Icc 0 (2 * Real.pi)) ∧
            ‖act (orderedProd fun k : Fin p =>
                NormedSpace.exp (-(Complex.I * (β k : ℂ)) • HI) *
                  NormedSpace.exp (-(Complex.I * (θ k : ℂ)) • HF)) (ψ 0) - ψ 1‖ ≤ ε := by
  intro ι _ _ HI HF hI hF s0 T hs0 hT ψ hψ ε hε
  exact QAOAC4.c4_gen HI HF hI hF s0 T hs0 hT ψ hψ ε hε

end C4Sec

/-! Statement check for the DECOMPOSE plan of 52c231a1
(QAlgorithms.Nannicini.qaoa_approximates_adiabatic). Each child is a `def ... : Prop`
so this file compiles without proofs. Path used: H(s) = (1-s) H_I + s H_F, frozen at s0 < 1 and
negated, so the Proved `adiabatic_theorem_linInterp` (sign +i) tracks the TOP eigenvector. -/

open QAlgorithms

namespace QAOAPlan52

/-- the reparametrised negated path `s ↦ -H(s * s0)` written as a `linInterp`. -/
noncomputable def negPath {n : ℕ} (f : Qubits n → ℝ) (s0 : ℝ) (s : ℝ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  linInterp (-qaoaMixer n) (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) s

/-- C1 (Perron–Frobenius + Weyl + compactness): for `s0 < 1` the top eigenvalue of `H(s s0)` is
simple with a uniform gap, and a continuous unit top-eigenvector path starts at `H^{⊗n}|0⟩`. -/
def C1 : Prop :=
  ∀ (n : ℕ) (f : Qubits n → ℝ) (s0 : ℝ), s0 ∈ Set.Ico (0 : ℝ) 1 →
    ∃ (lam : ℝ → ℝ) (φ : ℝ → EuclideanSpace ℂ (Qubits n)) (γ : ℝ), 0 < γ ∧
      ContinuousOn lam (Set.Icc 0 1) ∧ φ 0 = act (hadamardN n) (zeroKet n) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsState (φ s) ∧
        act (linInterp (-qaoaMixer n) (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) s)
          (φ s) = (lam s : ℂ) • φ s ∧
        HasGapAround
          (linInterp (-qaoaMixer n) (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) s)
          (lam s) γ ∧
        ∀ v : EuclideanSpace ℂ (Qubits n), lam s * ‖v‖ ^ 2 ≤ RCLike.re (inner ℂ v
          (act (linInterp (-qaoaMixer n) (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) s)
            v))

/-- C2 (variational): for `s0` close to 1 every unit top eigenvector of `H(s0)` (bottom of
`-H(s0)`) is `δ`-close to a unit top eigenvector of `H_F`. -/
def C2 : Prop :=
  ∀ (n : ℕ) (f : Qubits n → ℝ) (δ : ℝ), 0 < δ → ∃ s0 ∈ Set.Ico (0 : ℝ) 1,
    ∀ v : EuclideanSpace ℂ (Qubits n), IsState v → ∀ μ : ℝ,
      act (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) v = (μ : ℂ) • v →
      (∀ w : EuclideanSpace ℂ (Qubits n), μ * ‖w‖ ^ 2 ≤
        RCLike.re (inner ℂ w (act (-linInterp (qaoaMixer n) (problemHamiltonian f) s0) w))) →
      ∃ φ : EuclideanSpace ℂ (Qubits n), IsState φ ∧
        act (problemHamiltonian f) φ =
          ((Finset.univ.sup' Finset.univ_nonempty f : ℝ) : ℂ) • φ ∧ ‖v - φ‖ ≤ δ

/-- C3 (linear ODE existence, Picard–Lindelöf). -/
def C3 : Prop :=
  ∀ {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) (T : ℝ) (x : EuclideanSpace ℂ ι),
    ∃ ψ : ℝ → EuclideanSpace ℂ ι, SolvesAdiabaticPlus (linInterp A B) T ψ ∧ ψ 0 = x

/-- C4 (Trotterisation, Nannicini p.230 proof of Prop. 9.28), for general Hermitian `H_I, H_F`:
the adiabatic evolution along the negated path is approximated by alternating layers with angles
in `[0, 2π]`, for all large depths. PROVED: scratch/decomp/52c231a1/child_c4.lean. -/
def C4 : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (HI HF : Matrix ι ι ℂ), HI.IsHermitian →
      HF.IsHermitian → ∀ (s0 T : ℝ), s0 ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ T →
      ∀ ψ : ℝ → EuclideanSpace ℂ ι,
        SolvesAdiabaticPlus (linInterp (-HI) (-linInterp HI HF s0)) T ψ →
        ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, 1 ≤ P ∧ ∀ p : ℕ, P ≤ p →
          ∃ β θ : Fin p → ℝ, (∀ k, β k ∈ Set.Icc 0 (2 * Real.pi)) ∧
            (∀ k, θ k ∈ Set.Icc 0 (2 * Real.pi)) ∧
            ‖act (orderedProd fun k : Fin p =>
                NormedSpace.exp (-(Complex.I * (β k : ℂ)) • HI) *
                  NormedSpace.exp (-(Complex.I * (θ k : ℂ)) • HF)) (ψ 0) - ψ 1‖ ≤ ε

/-- C4a (Lie product formula, Hall *Lie Groups* Thm 2.11), sub-step of C4. -/
def C4a : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ),
    Filter.Tendsto (fun m : ℕ =>
      (NormedSpace.exp ((1 / (m : ℂ)) • A) * NormedSpace.exp ((1 / (m : ℂ)) • B)) ^ m)
      Filter.atTop (nhds (NormedSpace.exp (A + B)))

/-- C4b (piecewise-constant Hamiltonian approximation of the adiabatic solution), sub-step of C4. -/
def C4b : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ), A.IsHermitian → B.IsHermitian →
    ∀ (T : ℝ) (ψ : ℝ → EuclideanSpace ℂ ι), SolvesAdiabaticPlus (linInterp A B) T ψ →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
        ‖act (orderedProd (fun k : Fin N =>
            NormedSpace.exp ((Complex.I * ((T / N : ℝ) : ℂ)) • linInterp A B ((k : ℝ) / N))))
          (ψ 0) - ψ 1‖ ≤ ε

/-- the Proved `adiabatic_theorem_linInterp` (b52c41e17), at universe 0. -/
def AdiabaticLin : Prop :=
  ∃ c : ℝ, ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (HI HF : Matrix ι ι ℂ),
      HI.IsHermitian → HF.IsHermitian →
      ∀ (lam : ℝ → ℝ), ContinuousOn lam (Set.Icc 0 1) →
      ∀ (φ : ℝ → EuclideanSpace ℂ ι),
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsState (φ s) ∧ act (linInterp HI HF s) (φ s) = (lam s : ℂ) • φ s) →
      ∀ (γ : ℝ), 0 < γ →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (linInterp HI HF s) (lam s) γ) →
      ∀ (δ : ℝ), 0 < δ → ∀ (T : ℝ),
      c / δ * (specNorm (HF - HI) / γ ^ 2 + specNorm (HF - HI) ^ 2 / γ ^ 3) ≤ T →
      ∀ (ψ : ℝ → EuclideanSpace ℂ ι), SolvesAdiabaticPlus (linInterp HI HF) T ψ → ψ 0 = φ 0 →
      ∃ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) • ψ 1 - φ 1‖ ≤ δ

lemma act_smul' {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ) (x : EuclideanSpace ℂ ι) :
    act A (c • x) = c • act A x := by
  simp [act, Matrix.mulVec_smul]

/-- GLUE: the parent follows from AdiabaticLin + C1..C4. -/
theorem glue (hA : AdiabaticLin) (h1 : C1) (h2 : C2) (h3 : C3) (h4 : C4)
    {n : ℕ} (f : Qubits n → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ φ : EuclideanSpace ℂ (Qubits n), IsState φ ∧
      act (problemHamiltonian f) φ = ((Finset.univ.sup' Finset.univ_nonempty f : ℝ) : ℂ) • φ ∧
      ∃ P : ℕ, 1 ≤ P ∧ ∀ p : ℕ, P ≤ p →
        ∃ β θ : Fin p → ℝ, (∀ k, β k ∈ Set.Icc 0 (2 * Real.pi)) ∧
          (∀ k, θ k ∈ Set.Icc 0 (2 * Real.pi)) ∧
          ‖act (qaoaUnitary f p β θ) (act (hadamardN n) (zeroKet n)) - φ‖ ≤ δ := by
  obtain ⟨s0, hs0, hC2⟩ := h2 n f (δ / 2) (by linarith)
  obtain ⟨lam, φp, γ, hγ, hlam, hφ0, hpath⟩ := h1 n f s0 hs0
  set HI : Matrix (Qubits n) (Qubits n) ℂ := -qaoaMixer n with hHI
  set HF : Matrix (Qubits n) (Qubits n) ℂ :=
    -linInterp (qaoaMixer n) (problemHamiltonian f) s0 with hHF
  have hL0 : linInterp HI HF 0 = HI := by simp [linInterp]
  have hL1 : linInterp HI HF 1 = HF := by simp [linInterp]
  have hHIh : HI.IsHermitian := by
    have := (hpath 0 ⟨le_refl _, zero_le_one⟩).2.2.1.1
    rwa [hL0] at this
  have hHFh : HF.IsHermitian := by
    have := (hpath 1 ⟨zero_le_one, le_refl _⟩).2.2.1.1
    rwa [hL1] at this
  obtain ⟨c, hc⟩ := hA
  set T : ℝ := max 0 (c / (δ / 4) * (specNorm (HF - HI) / γ ^ 2 +
    specNorm (HF - HI) ^ 2 / γ ^ 3)) with hT
  obtain ⟨ψ, hψ, hψ0⟩ := h3 HI HF T (φp 0)
  obtain ⟨θ0, hθ0⟩ := hc HI HF hHIh hHFh lam hlam φp
    (fun s hs => ⟨(hpath s hs).1, (hpath s hs).2.1⟩) γ hγ (fun s hs => (hpath s hs).2.2.1)
    (δ / 4) (by linarith) T (le_max_right _ _) ψ hψ hψ0
  have hMixH : (qaoaMixer n).IsHermitian := by
    have := hHIh.neg
    rwa [hHI, neg_neg] at this
  have hPH : (problemHamiltonian f).IsHermitian := by
    unfold Matrix.IsHermitian problemHamiltonian
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext z
    simp
  obtain ⟨P, hP1, hP⟩ := h4 (qaoaMixer n) (problemHamiltonian f) hMixH hPH s0 T
    ⟨hs0.1, hs0.2.le⟩ (le_max_left _ _) ψ hψ (δ / 4) (by linarith)
  set u : ℂ := Complex.exp (((-θ0 : ℝ) : ℂ) * Complex.I) with hu
  have hun : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  set v := u • φp 1 with hv
  have h1p := hpath 1 ⟨zero_le_one, le_refl _⟩
  have hvS : IsState v := by
    have := h1p.1
    unfold IsState at this ⊢
    rw [hv, norm_smul, hun, this, one_mul]
  have hveig : act HF v = (lam 1 : ℂ) • v := by
    have := h1p.2.1
    rw [hL1] at this
    rw [hv, act_smul', this, smul_comm]
  have hvmin : ∀ w : EuclideanSpace ℂ (Qubits n), lam 1 * ‖w‖ ^ 2 ≤
      RCLike.re (inner ℂ w (act HF w)) := by
    intro w
    have := h1p.2.2.2 w
    rwa [hL1] at this
  obtain ⟨φ, hφS, hφe, hφd⟩ := hC2 v hvS (lam 1) hveig hvmin
  refine ⟨φ, hφS, hφe, P, hP1, fun p hp => ?_⟩
  obtain ⟨β, θ, hβ, hθ, hU0⟩ := hP p hp
  refine ⟨β, θ, hβ, hθ, ?_⟩
  have hU : ‖act (qaoaUnitary f p β θ) (ψ 0) - ψ 1‖ ≤ δ / 4 := hU0
  have hψ0' : ψ 0 = act (hadamardN n) (zeroKet n) := by rw [hψ0, hφ0]
  rw [hψ0'] at hU
  have hmid : ‖ψ 1 - v‖ ≤ δ / 4 := by
    have hrw : ψ 1 - v =
        u • (Complex.exp ((θ0 : ℂ) * Complex.I) • ψ 1 - φp 1) := by
      rw [smul_sub, smul_smul, hv, hu, ← Complex.exp_add]
      have : ((-θ0 : ℝ) : ℂ) * Complex.I + (θ0 : ℂ) * Complex.I = 0 := by
        push_cast; ring
      rw [this, Complex.exp_zero, one_smul]
    rw [hrw, norm_smul, hun, one_mul]
    exact hθ0
  calc ‖act (qaoaUnitary f p β θ) (act (hadamardN n) (zeroKet n)) - φ‖
      = ‖(act (qaoaUnitary f p β θ) (act (hadamardN n) (zeroKet n)) - ψ 1) +
          (ψ 1 - v) + (v - φ)‖ := by congr 1; abel
    _ ≤ ‖act (qaoaUnitary f p β θ) (act (hadamardN n) (zeroKet n)) - ψ 1‖ +
          ‖ψ 1 - v‖ + ‖v - φ‖ := norm_add₃_le
    _ ≤ δ / 4 + δ / 4 + δ / 2 := by gcongr
    _ = δ := by ring

end QAOAPlan52

theorem c1_solution : QAOAPlan52.C1 := fun n f s0 hs0 => C1Main.c1_main n f s0 hs0

theorem c2_solution' : QAOAPlan52.C2 := c2_solution

theorem c3_solution' : QAOAPlan52.C3 := c3_solution

theorem c4_solution' : QAOAPlan52.C4 := c4_solution

open QAlgorithms in
theorem solution {n : ℕ} (f : Qubits n → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ φ : EuclideanSpace ℂ (Qubits n), IsState φ ∧
      act (problemHamiltonian f) φ = ((Finset.univ.sup' Finset.univ_nonempty f : ℝ) : ℂ) • φ ∧
      ∃ P : ℕ, 1 ≤ P ∧ ∀ p : ℕ, P ≤ p →
        ∃ β θ : Fin p → ℝ, (∀ k, β k ∈ Set.Icc 0 (2 * Real.pi)) ∧
          (∀ k, θ k ∈ Set.Icc 0 (2 * Real.pi)) ∧
          ‖act (qaoaUnitary f p β θ) (act (hadamardN n) (zeroKet n)) - φ‖ ≤ δ := by
  exact QAOAPlan52.glue QAlgorithms.Nannicini.adiabatic_theorem_linInterp.{0} c1_solution
    c2_solution' c3_solution' c4_solution' f δ hδ
