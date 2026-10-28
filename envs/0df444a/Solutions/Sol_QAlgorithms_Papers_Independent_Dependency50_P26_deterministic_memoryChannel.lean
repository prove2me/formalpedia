-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.deterministic_memoryChannel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T20:27:26.432826+00:00
-- url     : https://prove2.me/submissions/ca639a19-5df7-4a59-9d45-750f8d69c9cc

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_deterministic_iff_normalized
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace P26DM

section step
variable {O I X J : Type*} [Fintype O] [Fintype I] [Fintype X] [Fintype J]

def psi (U : Matrix X X ℂ) (lam : X → ℝ) : X ⊕ J → X → ℂ
  | Sum.inl c, x => (Real.sqrt (lam c) : ℂ) * U x c
  | Sum.inr _, _ => 0

def phi (U' : Matrix (O × (I × X)) (O × (I × X)) ℂ) (lam' : O × (I × X) → ℝ)
    (y k : O × (I × X)) : ℂ := (Real.sqrt (lam' k) : ℂ) * U' y k

def psi' (U' : Matrix (O × (I × X)) (O × (I × X)) ℂ) (lam' : O × (I × X) → ℝ) :
    (O × (I × X)) ⊕ (I × (X ⊕ J)) → O × (I × X) → ℂ
  | Sum.inl k, y => phi U' lam' y k
  | Sum.inr _, _ => 0

def T (U : Matrix X X ℂ) (U' : Matrix (O × (I × X)) (O × (I × X)) ℂ) (lam' : O × (I × X) → ℝ)
    (i : I) (c : X) (o : O) (k : O × (I × X)) : ℂ :=
  ∑ x, phi U' lam' (o, (i, x)) k * conj (U x c)

def junk (lam : X → ℝ) : X ⊕ J → Prop
  | Sum.inl c => lam c = 0
  | Sum.inr _ => True

def V (o0 : O) (U : Matrix X X ℂ) (lam : X → ℝ) (U' : Matrix (O × (I × X)) (O × (I × X)) ℂ)
    (lam' : O × (I × X) → ℝ) :
    Matrix (O × ((O × (I × X)) ⊕ (I × (X ⊕ J)))) (I × (X ⊕ J)) ℂ :=
  fun p q => match p.2, q.2 with
    | Sum.inl k, Sum.inl c =>
        if lam c = 0 then 0 else ((Real.sqrt (lam c) : ℂ))⁻¹ * T U U' lam' q.1 c p.1 k
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr r, b => if p.1 = o0 ∧ r = q ∧ junk lam b then 1 else 0

lemma junk_psi (U : Matrix X X ℂ) (lam : X → ℝ) (b : X ⊕ J) (hb : junk lam b) (x : X) :
    psi U lam b x = 0 := by
  cases b with
  | inl c => simp only [junk] at hb; simp [psi, hb]
  | inr _ => rfl

lemma sqrt_sq_c (r : ℝ) (hr : 0 ≤ r) :
    (Real.sqrt r : ℂ) * conj (Real.sqrt r : ℂ) = (r : ℂ) := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hr]

variable (U : Matrix X X ℂ) (lam : X → ℝ) (U' : Matrix (O × (I × X)) (O × (I × X)) ℂ)
  (lam' : O × (I × X) → ℝ) (C : Matrix X X ℂ) (C' : Matrix (O × (I × X)) (O × (I × X)) ℂ)

lemma G1 (hlam' : ∀ k, 0 ≤ lam' k)
    (hC' : C' = U' * Matrix.diagonal (fun k => (lam' k : ℂ)) * U'ᴴ) (y y' : O × (I × X)) :
    ∑ k, phi U' lam' y k * conj (phi U' lam' y' k) = C' y y' := by
  rw [hC']
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, phi, map_mul, Complex.star_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := sqrt_sq_c (lam' k) (hlam' k)
  linear_combination U' y k * conj (U' y' k) * this

lemma UCU (hU : Uᴴ * U = 1) (hC : C = U * Matrix.diagonal (fun c => (lam c : ℂ)) * Uᴴ) :
    Uᴴ * C * U = Matrix.diagonal (fun c => (lam c : ℂ)) := by
  rw [hC, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU,
    Matrix.mul_one]

lemma G2 (hU : Uᴴ * U = 1) (hlam' : ∀ k, 0 ≤ lam' k)
    (hC : C = U * Matrix.diagonal (fun c => (lam c : ℂ)) * Uᴴ)
    (hC' : C' = U' * Matrix.diagonal (fun k => (lam' k : ℂ)) * U'ᴴ)
    (htl : traceLeft C' = Matrix.kronecker (1 : Matrix I I ℂ) C) (i i2 : I) (c c2 : X) :
    ∑ o, ∑ k, T U U' lam' i c o k * conj (T U U' lam' i2 c2 o k) =
      if i = i2 then (if c = c2 then (lam c : ℂ) else 0) else 0 := by
  have h1 : ∀ o k, T U U' lam' i c o k * conj (T U U' lam' i2 c2 o k) =
      ∑ x, ∑ x', conj (U x c) * U x' c2 *
        (phi U' lam' (o, (i, x)) k * conj (phi U' lam' (o, (i2, x')) k)) := by
    intro o k
    simp only [T, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring
  simp only [h1]
  have h2 : ∀ x x', ∑ o, ∑ k, conj (U x c) * U x' c2 *
      (phi U' lam' (o, (i, x)) k * conj (phi U' lam' (o, (i2, x')) k)) =
      conj (U x c) * U x' c2 * (if i = i2 then C x x' else 0) := by
    intro x x'
    simp_rw [← Finset.mul_sum, G1 U' lam' C' hlam' hC']
    congr 1
    have := congrArg (fun M => M (i, x) (i2, x')) htl
    simp only [traceLeft, Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply] at this
    rw [this]; split_ifs <;> simp
  set f : O → (O × (I × X)) → X → X → ℂ := fun o k x x' => conj (U x c) * U x' c2 *
      (phi U' lam' (o, (i, x)) k * conj (phi U' lam' (o, (i2, x')) k))
  calc ∑ o, ∑ k, ∑ x, ∑ x', f o k x x' = ∑ o, ∑ x, ∑ k, ∑ x', f o k x x' :=
        Finset.sum_congr rfl fun o _ => Finset.sum_comm
    _ = ∑ o, ∑ x, ∑ x', ∑ k, f o k x x' :=
        Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, ∑ o, ∑ x', ∑ k, f o k x x' := Finset.sum_comm
    _ = ∑ x, ∑ x', ∑ o, ∑ k, f o k x x' :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, ∑ x', conj (U x c) * U x' c2 * (if i = i2 then C x x' else 0) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => h2 x x'
    _ = _ := by
      have hd := congrArg (fun M => M c c2) (UCU U lam C hU hC)
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply] at hd
      split_ifs with hi hc
      · subst hc; rw [if_pos rfl] at hd; rw [← hd]
        simp only [mul_one, Finset.sum_mul, Complex.star_def]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring
      · rw [if_neg hc] at hd; rw [← hd]
        simp only [mul_one, Finset.sum_mul, Complex.star_def]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring
      · simp


variable {U lam U' lam' C C'}

lemma T_zero (hU : Uᴴ * U = 1) (hlam' : ∀ k, 0 ≤ lam' k)
    (hC : C = U * Matrix.diagonal (fun c => (lam c : ℂ)) * Uᴴ)
    (hC' : C' = U' * Matrix.diagonal (fun k => (lam' k : ℂ)) * U'ᴴ)
    (htl : traceLeft C' = Matrix.kronecker (1 : Matrix I I ℂ) C) (i : I) (c : X) (hc : lam c = 0)
    (o : O) (k : O × (I × X)) : T U U' lam' i c o k = 0 := by
  have h := G2 U lam U' lam' C C' hU hlam' hC hC' htl i i c c
  simp only [if_true, hc, Complex.ofReal_zero] at h
  have hn : ∀ o k, T U U' lam' i c o k * conj (T U U' lam' i c o k) =
      ((Complex.normSq (T U U' lam' i c o k) : ℝ) : ℂ) := fun o k => Complex.mul_conj _
  simp only [hn] at h
  have h0 : ∑ o, ∑ k, Complex.normSq (T U U' lam' i c o k) = 0 := by exact_mod_cast h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun o _ =>
    Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _)).mp h0 o (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg _)).mp h1 k
    (Finset.mem_univ _)
  exact Complex.normSq_eq_zero.mp h2

lemma amp (o0 : O) (hU : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hlam : ∀ c, 0 ≤ lam c)
    (hlam' : ∀ k, 0 ≤ lam' k)
    (hC : C = U * Matrix.diagonal (fun c => (lam c : ℂ)) * Uᴴ)
    (hC' : C' = U' * Matrix.diagonal (fun k => (lam' k : ℂ)) * U'ᴴ)
    (htl : traceLeft C' = Matrix.kronecker (1 : Matrix I I ℂ) C)
    (o : O) (i : I) (x : X) (a : (O × (I × X)) ⊕ (I × (X ⊕ J))) :
    ∑ b : X ⊕ J, V (J := J) o0 U lam U' lam' (o, a) (i, b) * psi U lam b x =
      psi' U' lam' a (o, (i, x)) := by
  cases a with
  | inl k =>
    rw [Fintype.sum_sum_type]
    simp only [V, psi, mul_zero, Finset.sum_const_zero, add_zero, psi']
    have hterm : ∀ c, (if lam c = 0 then 0 else ((Real.sqrt (lam c) : ℂ))⁻¹ *
        T U U' lam' i c o k) * ((Real.sqrt (lam c) : ℂ) * U x c) = T U U' lam' i c o k * U x c := by
      intro c
      split_ifs with hc
      · rw [T_zero hU hlam' hC hC' htl i c hc o k]; simp
      · have : (Real.sqrt (lam c) : ℂ) ≠ 0 := by
          rw [Complex.ofReal_ne_zero]
          intro h0
          rw [Real.sqrt_eq_zero'] at h0
          exact hc (le_antisymm h0 (hlam c))
        field_simp
    rw [Finset.sum_congr rfl fun c _ => hterm c]
    simp only [T, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hu : ∀ x', ∑ c, phi U' lam' (o, (i, x')) k * conj (U x' c) * U x c =
        phi U' lam' (o, (i, x')) k * (U * Uᴴ) x x' := by
      intro x'
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => by ring
    simp only [hu, hU2, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  | inr r =>
    simp only [V, psi']
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with h
    · rw [junk_psi U lam b h.2.2 x, mul_zero]
    · rw [zero_mul]


lemma partR (o0 : O) (i i2 : I) (b b2 : X ⊕ J) :
    ∑ o : O, ∑ r : I × (X ⊕ J),
      conj (if o = o0 ∧ r = (i, b) ∧ junk lam b then (1 : ℂ) else 0) *
        (if o = o0 ∧ r = (i2, b2) ∧ junk lam b2 then (1 : ℂ) else 0) =
      if (i, b) = (i2, b2) ∧ junk lam b then 1 else 0 := by
  rw [Finset.sum_eq_single o0 (fun o _ ho => by simp [ho]) (by simp)]
  rw [Finset.sum_eq_single (i, b) (fun r _ hr => by simp [hr]) (by simp)]
  by_cases h1 : (i, b) = (i2, b2)
  · simp only [Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    by_cases hj : junk lam b <;> simp [hj]
  · simp [h1]

lemma partL (o0 : O) (hU : Uᴴ * U = 1) (hlam : ∀ c, 0 ≤ lam c) (hlam' : ∀ k, 0 ≤ lam' k)
    (hC : C = U * Matrix.diagonal (fun c => (lam c : ℂ)) * Uᴴ)
    (hC' : C' = U' * Matrix.diagonal (fun k => (lam' k : ℂ)) * U'ᴴ)
    (htl : traceLeft C' = Matrix.kronecker (1 : Matrix I I ℂ) C) (i i2 : I) (b b2 : X ⊕ J) :
    ∑ o : O, ∑ k : O × (I × X),
      conj (V (J := J) o0 U lam U' lam' (o, Sum.inl k) (i, b)) *
        V (J := J) o0 U lam U' lam' (o, Sum.inl k) (i2, b2) =
      if (i, b) = (i2, b2) ∧ ¬ junk lam b then 1 else 0 := by
  cases b with
  | inr j => simp [V, junk]
  | inl c =>
    cases b2 with
    | inr j2 => simp [V]
    | inl c2 =>
      simp only [V]
      by_cases hc : lam c = 0
      · simp [hc, junk]
      by_cases hc2 : lam c2 = 0
      · simp only [hc2, if_true, mul_zero, Finset.sum_const_zero]
        rw [if_neg]; rintro ⟨h1, -⟩
        simp only [Prod.mk.injEq, Sum.inl.injEq] at h1
        exact hc (h1.2 ▸ hc2)
      simp only [hc, hc2, if_false, map_mul]
      have hg := G2 U lam U' lam' C C' hU hlam' hC hC' htl i i2 c c2
      have hconj : ∑ o, ∑ k, conj (T U U' lam' i c o k) * T U U' lam' i2 c2 o k =
          if i = i2 then (if c = c2 then (lam c : ℂ) else 0) else 0 := by
        calc ∑ o, ∑ k, conj (T U U' lam' i c o k) * T U U' lam' i2 c2 o k =
            conj (∑ o, ∑ k, T U U' lam' i c o k * conj (T U U' lam' i2 c2 o k)) := by
              simp only [map_sum, map_mul, Complex.conj_conj]
          _ = _ := by rw [hg]; split_ifs <;> simp
      have e : ∀ o k, conj (((Real.sqrt (lam c) : ℂ))⁻¹) * conj (T U U' lam' i c o k) *
          ((((Real.sqrt (lam c2) : ℂ))⁻¹) * T U U' lam' i2 c2 o k) =
          (((Real.sqrt (lam c) : ℂ))⁻¹ * ((Real.sqrt (lam c2) : ℂ))⁻¹) *
            (conj (T U U' lam' i c o k) * T U U' lam' i2 c2 o k) := by
        intro o k; rw [map_inv₀, Complex.conj_ofReal]; ring
      simp only [e, ← Finset.mul_sum, hconj]
      have hs : (Real.sqrt (lam c) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]; intro h0; rw [Real.sqrt_eq_zero'] at h0
        exact hc (le_antisymm h0 (hlam c))
      by_cases hi : i = i2
      · by_cases hcc : c = c2
        · subst hi hcc
          simp only [if_true, junk, hc, not_false_eq_true, and_self]
          have : (lam c : ℂ) = (Real.sqrt (lam c) : ℂ) * (Real.sqrt (lam c) : ℂ) := by
            rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hlam c)]
          rw [this]; field_simp
        · simp [hi, hcc]
      · simp [hi]

lemma iso (o0 : O) (hU : Uᴴ * U = 1) (hlam : ∀ c, 0 ≤ lam c) (hlam' : ∀ k, 0 ≤ lam' k)
    (hC : C = U * Matrix.diagonal (fun c => (lam c : ℂ)) * Uᴴ)
    (hC' : C' = U' * Matrix.diagonal (fun k => (lam' k : ℂ)) * U'ᴴ)
    (htl : traceLeft C' = Matrix.kronecker (1 : Matrix I I ℂ) C) :
    (V (J := J) o0 U lam U' lam')ᴴ * V (J := J) o0 U lam U' lam' = 1 := by
  ext ⟨i, b⟩ ⟨i2, b2⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Fintype.sum_sum_type,
    Finset.sum_add_distrib]
  rw [partL o0 hU hlam hlam' hC hC' htl i i2 b b2]
  have hR := partR (lam := lam) o0 i i2 b b2
  simp only [V] at hR ⊢
  rw [hR, Matrix.one_apply]
  by_cases h : (i, b) = (i2, b2)
  · by_cases hj : junk lam b <;> simp [h, hj]
  · simp [h]

lemma psi'_eq (U' : Matrix (O × (I × X)) (O × (I × X)) ℂ) (lam' : O × (I × X) → ℝ)
    (a : (O × (I × X)) ⊕ (I × (X ⊕ J))) (y : O × (I × X)) :
    psi' U' lam' a y = psi U' lam' a y := by
  cases a <;> rfl

lemma diag_of_e {Z : Type*} [Fintype Z] [DecidableEq Z] (C U : Matrix Z Z ℂ) (lam : Z → ℝ)
    (h : ∀ y y', C y y' = ∑ k, U y k * (lam k : ℂ) * conj (U y' k)) :
    C = U * Matrix.diagonal (fun k => (lam k : ℂ)) * Uᴴ := by
  ext y y'
  rw [h]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.star_def]

lemma tl_of_e (C : Matrix X X ℂ) (C' : Matrix (O × (I × X)) (O × (I × X)) ℂ)
    (h : ∀ i i2 x x', ∑ o, C' (o, (i, x)) (o, (i2, x')) = if i = i2 then C x x' else 0) :
    traceLeft C' = Matrix.kronecker (1 : Matrix I I ℂ) C := by
  ext ⟨i, x⟩ ⟨i2, x'⟩
  simp only [traceLeft, Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  rw [h]; split_ifs <;> simp

lemma amp_e (o0 : O) (hU : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hlam : ∀ c, 0 ≤ lam c)
    (hlam' : ∀ k, 0 ≤ lam' k)
    (hC : ∀ y y', C y y' = ∑ k, U y k * (lam k : ℂ) * conj (U y' k))
    (hC' : ∀ y y', C' y y' = ∑ k, U' y k * (lam' k : ℂ) * conj (U' y' k))
    (htl : ∀ i i2 x x', ∑ o, C' (o, (i, x)) (o, (i2, x')) = if i = i2 then C x x' else 0)
    (o : O) (i : I) (x : X) (a : (O × (I × X)) ⊕ (I × (X ⊕ J))) :
    ∑ b : X ⊕ J, V (J := J) o0 U lam U' lam' (o, a) (i, b) * psi U lam b x =
      psi U' lam' a (o, (i, x)) := by
  rw [← psi'_eq]
  exact amp o0 hU hU2 hlam hlam' (diag_of_e C U lam hC) (diag_of_e C' U' lam' hC')
    (tl_of_e C C' htl) o i x a

lemma iso_e (o0 : O) (hU : Uᴴ * U = 1) (hlam : ∀ c, 0 ≤ lam c) (hlam' : ∀ k, 0 ≤ lam' k)
    (hC : ∀ y y', C y y' = ∑ k, U y k * (lam k : ℂ) * conj (U y' k))
    (hC' : ∀ y y', C' y y' = ∑ k, U' y k * (lam' k : ℂ) * conj (U' y' k))
    (htl : ∀ i i2 x x', ∑ o, C' (o, (i, x)) (o, (i2, x')) = if i = i2 then C x x' else 0)
    (q q2 : I × (X ⊕ J)) :
    ∑ p, conj (V (J := J) o0 U lam U' lam' p q) * V (J := J) o0 U lam U' lam' p q2 =
      if q = q2 then 1 else 0 := by
  have h := congrArg (fun M => M q q2) (iso o0 hU hlam hlam' (diag_of_e C U lam hC)
    (diag_of_e C' U' lam' hC') (tl_of_e C C' htl))
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Matrix.one_apply] at h
  rw [h]

lemma kron_one_congr {A W : Type*} (M : Matrix A A ℂ) {d1 d2 : DecidableEq W} :
    Matrix.kronecker (@OfNat.ofNat (Matrix W W ℂ) 1 (@One.toOfNat1 _ (@Matrix.one W ℂ d1 _ _))) M =
      Matrix.kronecker
        (@OfNat.ofNat (Matrix W W ℂ) 1 (@One.toOfNat1 _ (@Matrix.one W ℂ d2 _ _))) M := by
  obtain rfl : d1 = d2 := Subsingleton.elim _ _
  rfl

end step

end P26DM

namespace QAlgorithms.Papers.Independent.Dependency50.P26
open P26DM

/-! ## chains -/

def dmUp (s : Signature) (j : ℕ) (M : Matrix (Basis s j) (Basis s j) ℂ) :
    Matrix (Basis s (j+1)) (Basis s (j+1)) ℂ :=
  ((Fintype.card (Fin (s.output j)) : ℂ)⁻¹) •
    Matrix.kronecker (1 : Matrix (Fin (s.output j)) (Fin (s.output j)) ℂ)
      (Matrix.kronecker (1 : Matrix (Fin (s.input j)) (Fin (s.input j)) ℂ) M)

lemma dm_tl_kron {α β : Type*} [Fintype α] (A : Matrix α α ℂ) (D : Matrix β β ℂ) :
    traceLeft (Matrix.kronecker A D) = A.trace • D := by
  ext b b'
  simp [traceLeft, Matrix.kronecker, Matrix.trace, Finset.sum_mul]

lemma dmUp_tl (s : Signature) (j : ℕ) (M : Matrix (Basis s j) (Basis s j) ℂ) :
    traceLeft (dmUp s j M) =
      Matrix.kronecker (1 : Matrix (Fin (s.input j)) (Fin (s.input j)) ℂ) M := by
  have hpos : (Fintype.card (Fin (s.output j)) : ℂ) ≠ 0 := by
    simp only [Fintype.card_fin]; exact_mod_cast (s.output_pos j).ne'
  unfold dmUp
  have : traceLeft (((Fintype.card (Fin (s.output j)) : ℂ)⁻¹) •
      Matrix.kronecker (1 : Matrix (Fin (s.output j)) (Fin (s.output j)) ℂ)
        (Matrix.kronecker (1 : Matrix (Fin (s.input j)) (Fin (s.input j)) ℂ) M)) =
      ((Fintype.card (Fin (s.output j)) : ℂ)⁻¹) • traceLeft
        (Matrix.kronecker (1 : Matrix (Fin (s.output j)) (Fin (s.output j)) ℂ)
          (Matrix.kronecker (1 : Matrix (Fin (s.input j)) (Fin (s.input j)) ℂ) M)) := by
    ext b b'; simp [traceLeft]; ring
  rw [this, dm_tl_kron, Matrix.trace_one, smul_smul, inv_mul_cancel₀ hpos, one_smul]

lemma dmUp_psd (s : Signature) (j : ℕ) (M : Matrix (Basis s j) (Basis s j) ℂ)
    (hM : M.PosSemidef) : (dmUp s j M).PosSemidef := by
  unfold dmUp
  refine Matrix.PosSemidef.smul ?_ ?_
  · exact Matrix.PosSemidef.one.kronecker (Matrix.PosSemidef.one.kronecker hM)
  · exact inv_nonneg.mpr (by exact_mod_cast (Nat.zero_le _))

def dmUpChain (s : Signature) : (j : ℕ) → Matrix (Basis s j) (Basis s j) ℂ
  | 0 => 1
  | j + 1 => dmUp s j (dmUpChain s j)

def dmExt (s : Signature) (n : ℕ) (C' : (j : ℕ) → Matrix (Basis s j) (Basis s j) ℂ)
    (R : Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ) : (j : ℕ) → Matrix (Basis s j) (Basis s j) ℂ
  | 0 => C' 0
  | j + 1 => if j + 1 ≤ n then C' (j+1) else
      if h : j = n then (h ▸ R) else dmUp s j (dmExt s n C' R j)

def IsChain (s : Signature) (C : (j : ℕ) → Matrix (Basis s j) (Basis s j) ℂ) : Prop :=
  C 0 = 1 ∧ (∀ j, (C j).PosSemidef) ∧
    ∀ j, traceLeft (C (j+1)) =
      Matrix.kronecker (1 : Matrix (Fin (s.input j)) (Fin (s.input j)) ℂ) (C j)

lemma chain_exists (s : Signature) : ∀ (n : ℕ) (R : Matrix (Basis s n) (Basis s n) ℂ),
    Normalized s n R → ∃ C, IsChain s C ∧ C n = R := by
  intro n
  induction n with
  | zero =>
    intro R hR
    refine ⟨dmUpChain s, ⟨rfl, ?_, fun j => dmUp_tl s j _⟩, hR.symm⟩
    intro j
    induction j with
    | zero => exact Matrix.PosSemidef.one
    | succ j ih => exact dmUp_psd s j _ ih
  | succ n ih =>
    intro R hR
    obtain ⟨hRp, Q, hQ, htlR⟩ := hR
    obtain ⟨C', ⟨hC'0, hC'p, hC'tl⟩, hC'n⟩ := ih Q hQ
    have hle : ∀ j, j ≤ n → dmExt s n C' R j = C' j := by
      intro j hj
      cases j with
      | zero => rfl
      | succ j => simp only [dmExt, if_pos hj]
    have htop : dmExt s n C' R (n+1) = R := by
      simp only [dmExt, show ¬ (n + 1 ≤ n) by omega, if_false]
      exact dif_pos trivial
    have hgt : ∀ j, n < j → dmExt s n C' R (j+1) = dmUp s j (dmExt s n C' R j) := by
      intro j hj
      simp only [dmExt, show ¬ (j + 1 ≤ n) by omega, if_false, dif_neg (show j ≠ n by omega)]
    refine ⟨dmExt s n C' R, ⟨hC'0, ?_, ?_⟩, htop⟩
    · intro j
      induction j with
      | zero => exact hC'p 0
      | succ j ihj =>
        rcases lt_trichotomy j n with h | h | h
        · rw [hle (j+1) h]; exact hC'p _
        · subst h; rw [htop]; exact hRp
        · rw [hgt j h]; exact dmUp_psd s j _ ihj
    · intro j
      rcases lt_trichotomy j n with h | h | h
      · rw [hle (j+1) h, hle j h.le]; exact hC'tl j
      · subst h; rw [htop, hle j le_rfl, hC'n]; exact htlR
      · rw [hgt j h]; exact dmUp_tl s j _


/-! ## the network -/

def Junk (s : Signature) : ℕ → Type
  | 0 => Empty
  | j + 1 => Fin (s.input j) × (Basis s j ⊕ Junk s j)

instance junkFintype (s : Signature) : (j : ℕ) → Fintype (Junk s j)
  | 0 => inferInstanceAs (Fintype Empty)
  | j + 1 => letI := junkFintype s j
             inferInstanceAs (Fintype (Fin (s.input j) × (Basis s j ⊕ Junk s j)))

abbrev MemT (s : Signature) (j : ℕ) := Basis s j ⊕ Junk s j

section net
variable (s : Signature) (C : (j : ℕ) → Matrix (Basis s j) (Basis s j) ℂ) (hC : IsChain s C)

def eU : (j : ℕ) → Matrix (Basis s j) (Basis s j) ℂ
  | 0 => 1
  | j + 1 => ((hC.2.1 (j+1)).1.eigenvectorUnitary : Matrix (Basis s (j+1)) (Basis s (j+1)) ℂ)

def eL : (j : ℕ) → Basis s j → ℝ
  | 0 => fun _ => 1
  | j + 1 => (hC.2.1 (j+1)).1.eigenvalues

lemma eU_unit (j : ℕ) : (eU s C hC j)ᴴ * eU s C hC j = 1 ∧ eU s C hC j * (eU s C hC j)ᴴ = 1 := by
  cases j with
  | zero => simp [eU]
  | succ j =>
    simp only [eU, ← Matrix.star_eq_conjTranspose]
    exact ⟨Unitary.star_mul_self_of_mem (hC.2.1 (j+1)).1.eigenvectorUnitary.2,
      Unitary.mul_star_self_of_mem (hC.2.1 (j+1)).1.eigenvectorUnitary.2⟩

lemma eL_nonneg (j : ℕ) (c : Basis s j) : 0 ≤ eL s C hC j c := by
  cases j with
  | zero => simp [eL]
  | succ j => exact (hC.2.1 (j+1)).eigenvalues_nonneg c

lemma eC (j : ℕ) : C j = eU s C hC j * Matrix.diagonal (fun c => (eL s C hC j c : ℂ)) *
    (eU s C hC j)ᴴ := by
  cases j with
  | zero =>
    rw [hC.1]; simp only [eU, eL, Complex.ofReal_one, Matrix.one_mul, Matrix.conjTranspose_one,
      Matrix.mul_one]
    exact Matrix.diagonal_one.symm
  | succ j =>
    have h := (hC.2.1 (j+1)).1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h
    exact h

def mem (j : ℕ) : ℕ := Fintype.card (MemT s j)

def eqv (j : ℕ) : Fin (mem s j) ≃ MemT s j := (Fintype.equivFin (MemT s j)).symm

def o0 (j : ℕ) : Fin (s.output j) := ⟨0, s.output_pos j⟩

abbrev PP (j : ℕ) := Fin (s.output j) × (Fin (s.input j) × Basis s j)

def eU' (j : ℕ) : Matrix (PP s j) (PP s j) ℂ := eU s C hC (j+1)

def eL' (j : ℕ) : PP s j → ℝ := eL s C hC (j+1)

def Vj (j : ℕ) : Matrix (Fin (s.output j) × MemT s (j+1)) (Fin (s.input j) × MemT s j) ℂ :=
  V (J := Junk s j) (o0 s j) (eU s C hC j) (eL s C hC j) (eU' s C hC j) (eL' s C hC j)

lemma eCe (j : ℕ) (y y' : Basis s j) :
    C j y y' = ∑ k, eU s C hC j y k * (eL s C hC j k : ℂ) * conj (eU s C hC j y' k) := by
  rw [eC s C hC j]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.star_def]

include hC in
lemma htle (j : ℕ) (i i2 : Fin (s.input j)) (x x' : Basis s j) :
    ∑ o : Fin (s.output j), C (j+1) (o, (i, x)) (o, (i2, x')) =
      @ite ℂ (i = i2) (Classical.decEq _ i i2) (C j x x') 0 := by
  have h := congrArg (fun M => M (i, x) (i2, x')) (hC.2.2 j)
  simp only [traceLeft, Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply] at h
  rw [h]; by_cases hi : i = i2 <;> simp [hi]

lemma Vj_iso (j : ℕ) (q q2 : Fin (s.input j) × MemT s j) :
    ∑ p, conj (Vj s C hC j p q) * Vj s C hC j p q2 = if q = q2 then 1 else 0 := by
  refine (iso_e (O := Fin (s.output j)) (I := Fin (s.input j)) (X := Basis s j) (J := Junk s j)
    (o0 s j) (eU_unit s C hC j).1 (eL_nonneg s C hC j) (eL_nonneg s C hC (j+1))
    (eCe s C hC j) (eCe s C hC (j+1)) (htle s C hC j) q q2).trans ?_
  by_cases hq : q = q2 <;> simp [hq]

lemma Vj_amp (j : ℕ) (o : Fin (s.output j)) (i : Fin (s.input j)) (x : Basis s j)
    (a : MemT s (j+1)) :
    ∑ b : MemT s j, Vj s C hC j (o, a) (i, b) * psi (eU s C hC j) (eL s C hC j) b x =
      psi (J := Junk s (j+1)) (eU s C hC (j+1)) (eL s C hC (j+1)) a (o, (i, x)) :=
  amp_e (O := Fin (s.output j)) (I := Fin (s.input j)) (X := Basis s j) (J := Junk s j)
    (o0 s j) (eU_unit s C hC j).1 (eU_unit s C hC j).2 (eL_nonneg s C hC j)
    (eL_nonneg s C hC (j+1)) (eCe s C hC j) (eCe s C hC (j+1)) (htle s C hC j) o i x a

def inter (j : ℕ) : Matrix (Fin (s.output j) × Fin (mem s (j+1)))
    (Fin (s.input j) × Fin (mem s j)) ℂ :=
  fun p q => Vj s C hC j (p.1, eqv s (j+1) p.2) (q.1, eqv s j q.2)

def net : IsometricNetwork s where
  memory := mem s
  memory_pos j := Fintype.card_pos
  initial_memory := by
    simp only [mem, MemT, Fintype.card_sum]
    show Fintype.card Unit + Fintype.card Empty = 1
    simp
  interaction j := inter s C hC j
  isometry j := by
    ext q q2
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.conjTranspose_apply, Complex.star_def, inter]
    rw [Fintype.sum_prod_type]
    have key : ∀ o : Fin (s.output j),
        ∑ m : Fin (mem s (j+1)), conj (Vj s C hC j (o, eqv s (j+1) m) (q.1, eqv s j q.2)) *
          Vj s C hC j (o, eqv s (j+1) m) (q2.1, eqv s j q2.2) =
        ∑ m : MemT s (j+1), conj (Vj s C hC j (o, m) (q.1, eqv s j q.2)) *
          Vj s C hC j (o, m) (q2.1, eqv s j q2.2) := fun o =>
      Equiv.sum_comp (eqv s (j+1)) (fun m => conj (Vj s C hC j (o, m) (q.1, eqv s j q.2)) *
          Vj s C hC j (o, m) (q2.1, eqv s j q2.2))
    simp only [key]
    rw [← Fintype.sum_prod_type (f := fun p : Fin (s.output j) × MemT s (j+1) =>
      conj (Vj s C hC j p (q.1, eqv s j q.2)) * Vj s C hC j p (q2.1, eqv s j q2.2))]
    rw [Vj_iso s C hC j]
    have e : (q.1, eqv s j q.2) = (q2.1, eqv s j q2.2) ↔ q = q2 := by
      constructor
      · intro h'; simp only [Prod.mk.injEq] at h'
        exact Prod.ext h'.1 ((eqv s j).injective h'.2)
      · rintro rfl; rfl
    by_cases h : q = q2
    · rw [if_pos (e.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (e.mp h')), if_neg h]

lemma net_amp : ∀ (j : ℕ) (a : Fin ((net s C hC).memory j)) (x : Basis s j),
    (net s C hC).amplitude j a x = psi (eU s C hC j) (eL s C hC j) (eqv s j a) x := by
  intro j
  induction j with
  | zero =>
    intro a x
    have ha : eqv s 0 a = Sum.inl () := by
      rcases h : eqv s 0 a with u | e
      · rfl
      · exact e.elim
    have ha0 : a.val = 0 := by
      have h1 : (net s C hC).memory 0 = 1 := (net s C hC).initial_memory
      have h2 := a.isLt; omega
    simp only [IsometricNetwork.amplitude, ha0, if_true, ha, psi, eU, eL, Real.sqrt_one,
      Complex.ofReal_one, one_mul]
    show (1:ℂ) = (1 : Matrix (Basis s 0) (Basis s 0) ℂ) x x
    rw [Matrix.one_apply_eq]
  | succ j ih =>
    intro a x
    simp only [IsometricNetwork.amplitude]
    simp only [ih]
    rw [show (net s C hC).interaction j = inter s C hC j from rfl]
    simp only [inter]
    have := Equiv.sum_comp (eqv s j) (fun b => Vj s C hC j (x.1, eqv s (j+1) a) (x.2.1, b) *
      psi (eU s C hC j) (eL s C hC j) b x.2.2)
    exact this.trans (Vj_amp s C hC j x.1 x.2.1 x.2.2 (eqv s (j+1) a))

lemma net_choi (n : ℕ) : (net s C hC).choi n = C n := by
  ext y y'
  simp only [IsometricNetwork.choi, Matrix.sum_apply, rankOne, net_amp]
  have := Equiv.sum_comp (eqv s n) (fun b => psi (eU s C hC n) (eL s C hC n) b y *
    conj (psi (eU s C hC n) (eL s C hC n) b y'))
  refine this.trans ?_
  rw [Fintype.sum_sum_type, eCe s C hC n]
  simp only [psi, zero_mul, Finset.sum_const_zero, add_zero, map_mul, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := sqrt_sq_c (eL s C hC n k) (eL_nonneg s C hC n k)
  rw [Complex.conj_ofReal] at h
  linear_combination eU s C hC n y k * conj (eU s C hC n y' k) * h

end net

end QAlgorithms.Papers.Independent.Dependency50.P26

open QAlgorithms.Papers.Independent.Dependency50.P26 in
theorem solution (s : QAlgorithms.Papers.Independent.Dependency50.P26.Signature) (n : ℕ)
    (hn : 0 < n)
    (R : Matrix (QAlgorithms.Papers.Independent.Dependency50.P26.Basis s n)
      (QAlgorithms.Papers.Independent.Dependency50.P26.Basis s n) ℂ)
    (hR : QAlgorithms.Papers.Independent.Dependency50.P26.Deterministic n s R) :
    ∃ net : QAlgorithms.Papers.Independent.Dependency50.P26.IsometricNetwork s,
      net.choi n = R := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpsd : R.PosSemidef := by
    cases m with
    | zero => exact hR.1
    | succ m => exact hR.1
  have hN := (deterministic_iff_normalized s (m+1) hn R hpsd).mp hR
  obtain ⟨C, hC, hCn⟩ := chain_exists s (m+1) R hN
  exact ⟨net s C hC, by rw [net_choi, hCn]⟩

