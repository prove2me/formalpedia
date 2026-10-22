-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P16.maximum_attained
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:04:29.71447+00:00
-- url     : https://prove2.me/submissions/4f636fa1-207d-4a18-9f13-dcf7d15046a9

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16
noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

open scoped ComplexConjugate



lemma g72gk1_m_tP_mul {d n : ℕ} (s t : Equiv.Perm (Fin n)) :
    Schur.tensorPermutation d n s * Schur.tensorPermutation d n t = Schur.tensorPermutation d n (s * t) := by
  ext y x
  simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (x ∘ t.symm)]
  · simp only [if_true]
    congr 1
  · intro b _ hb; simp [hb]
  · simp

lemma g72gk1_m_P_tP {d n : ℕ} (t : Equiv.Perm (Fin n)) :
    boseProjector d n * Schur.tensorPermutation d n t = boseProjector d n := by
  rw [boseProjector, Matrix.smul_mul, Finset.sum_mul]
  simp only [g72gk1_m_tP_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight t) _ _ (fun _ => rfl)

lemma g72gk1_m_tP_P {d n : ℕ} (t : Equiv.Perm (Fin n)) :
    Schur.tensorPermutation d n t * boseProjector d n = boseProjector d n := by
  rw [boseProjector, Matrix.mul_smul, Finset.mul_sum]
  simp only [g72gk1_m_tP_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft t) _ _ (fun _ => rfl)

lemma g72gk1_m_PP {d n : ℕ} : boseProjector d n * boseProjector d n = boseProjector d n := by
  nth_rewrite 1 [boseProjector]
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp only [g72gk1_m_tP_P, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin n))).ne'), one_smul]

lemma g72gk1_m_prod_delta {d N M : ℕ} (h : N ≤ M) (x y : Word M d) :
    (∏ k : Fin (M - N), if x ⟨N + k.val, by omega⟩ = y ⟨N + k.val, by omega⟩ then (1 : ℂ) else 0) =
      if (∀ j : Fin M, N ≤ j.val → x j = y j) then 1 else 0 := by
  rw [Finset.prod_boole]
  congr 1
  apply propext
  constructor
  · intro H j hj
    have := H ⟨j.val - N, by omega⟩ (Finset.mem_univ _)
    convert this using 2 <;> ext <;> simp <;> omega
  · intro H k _
    exact H _ (by simp)

lemma g72gk1_m_tWI_apply {d N M : ℕ} (h : N ≤ M) (A : TensorMat d N) (x y : Word M d) :
    tensorWithIdentity h A x y = A (fun k => x ⟨k.val, by omega⟩) (fun k => y ⟨k.val, by omega⟩) *
      if (∀ j : Fin M, N ≤ j.val → x j = y j) then 1 else 0 := by
  rw [tensorWithIdentity, g72gk1_m_prod_delta h]

lemma g72gk1_m_tWI_tWI {d N M R : ℕ} (h1 : N ≤ M) (h2 : M ≤ R) (A : TensorMat d N) :
    tensorWithIdentity h2 (tensorWithIdentity h1 A) = tensorWithIdentity (h1.trans h2) A := by
  ext x y
  rw [g72gk1_m_tWI_apply, g72gk1_m_tWI_apply, g72gk1_m_tWI_apply]
  by_cases H : ∀ j : Fin R, N ≤ j.val → x j = y j
  · have H2 : ∀ j : Fin R, M ≤ j.val → x j = y j := fun j hj => H j (by omega)
    have H1 : ∀ j : Fin M, N ≤ j.val → x ⟨j.val, by omega⟩ = y ⟨j.val, by omega⟩ :=
      fun j hj => H _ (by simpa using hj)
    rw [if_pos H1, if_pos H2, if_pos H, mul_one, mul_one]
  · rw [if_neg H, mul_zero]
    by_cases H2 : ∀ j : Fin R, M ≤ j.val → x j = y j
    · rw [if_pos H2, mul_one]
      have H1 : ¬ ∀ j : Fin M, N ≤ j.val → x ⟨j.val, by omega⟩ = y ⟨j.val, by omega⟩ := by
        intro H1; apply H; intro j hj
        by_cases hjM : j.val < M
        · exact H1 ⟨j.val, hjM⟩ hj
        · exact H2 j (by omega)
      rw [if_neg H1, mul_zero]
    · rw [if_neg H2, mul_zero]

def g72gk1_m_split {d N M : ℕ} (h : N ≤ M) : Word M d ≃ Word N d × Word (M - N) d where
  toFun x := (fun k => x ⟨k.val, by omega⟩, fun k => x ⟨N + k.val, by omega⟩)
  invFun z := fun j => if hj : j.val < N then z.1 ⟨j.val, hj⟩ else z.2 ⟨j.val - N, by omega⟩
  left_inv x := by
    funext j
    by_cases hj : j.val < N
    · simp [hj]
    · simp only [hj, dif_neg, not_false_eq_true]
      congr 1; ext; simp; omega
  right_inv z := by
    ext k
    · simp
    · simp

lemma g72gk1_m_tWI_mul {d N M : ℕ} (h : N ≤ M) (A B : TensorMat d N) :
    tensorWithIdentity h (A * B) = tensorWithIdentity h A * tensorWithIdentity h B := by
  ext x y
  rw [Matrix.mul_apply, ← (g72gk1_m_split h).symm.sum_comp, Fintype.sum_prod_type]
  simp only [g72gk1_m_tWI_apply, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_eq_single (g72gk1_m_split h x).2]
  · have e1 : (fun k : Fin N => (g72gk1_m_split h).symm (u, (g72gk1_m_split h x).2) ⟨k.val, by omega⟩) = u := by
      ext k; simp [g72gk1_m_split]
    have hx : ∀ j : Fin M, N ≤ j.val → x j = (g72gk1_m_split h).symm (u, (g72gk1_m_split h x).2) j := by
      intro j hj
      simp only [g72gk1_m_split, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, dif_neg (show ¬ j.val < N by omega)]
      congr 1; ext; simp; omega
    rw [e1, if_pos hx]
    by_cases H : ∀ j : Fin M, N ≤ j.val → x j = y j
    · rw [if_pos H, if_pos (fun j hj => (hx j hj).symm.trans (H j hj))]; ring
    · rw [if_neg H, if_neg (fun H' => H (fun j hj => (hx j hj).trans (H' j hj)))]; ring
  · intro v _ hv
    have : ¬ ∀ j : Fin M, N ≤ j.val → x j = (g72gk1_m_split h).symm (u, v) j := by
      intro H; apply hv; ext k
      have := H ⟨N + k.val, by omega⟩ (by simp)
      simp only [g72gk1_m_split, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk] at this ⊢
      rw [this, dif_neg (by simp)]; congr 1; ext; simp
    rw [if_neg this]; ring
  · simp

lemma g72gk1_m_tWI_smul {d N M : ℕ} (h : N ≤ M) (c : ℂ) (A : TensorMat d N) :
    tensorWithIdentity h (c • A) = c • tensorWithIdentity h A := by
  ext x y; simp only [g72gk1_m_tWI_apply, Matrix.smul_apply, smul_eq_mul]; ring

lemma g72gk1_m_tWI_sum {d N M : ℕ} (h : N ≤ M) {ι : Type*} (s : Finset ι) (A : ι → TensorMat d N) :
    tensorWithIdentity h (∑ i ∈ s, A i) = ∑ i ∈ s, tensorWithIdentity h (A i) := by
  ext x y; simp only [g72gk1_m_tWI_apply, Matrix.sum_apply, Finset.sum_mul]

def g72gk1_m_emb {M R : ℕ} (h : M ≤ R) : Fin M ≃ {k : Fin R // k.val < M} where
  toFun i := ⟨⟨i.val, by omega⟩, i.2⟩
  invFun k := ⟨k.1.val, k.2⟩
  left_inv i := rfl
  right_inv k := rfl

def g72gk1_m_ext {M R : ℕ} (h : M ≤ R) (t : Equiv.Perm (Fin M)) : Equiv.Perm (Fin R) :=
  t.extendDomain (g72gk1_m_emb h)

lemma g72gk1_m_ext_symm_lt {M R : ℕ} (h : M ≤ R) (t : Equiv.Perm (Fin M)) (j : Fin R) (hj : j.val < M) :
    (g72gk1_m_ext h t).symm j = ⟨(t.symm ⟨j.val, hj⟩).val, by omega⟩ := by
  have e : (g72gk1_m_ext h t).symm = g72gk1_m_ext h t⁻¹ := by
    rw [g72gk1_m_ext, g72gk1_m_ext, ← Equiv.Perm.extendDomain_inv]; rfl
  rw [e, g72gk1_m_ext, Equiv.Perm.extendDomain_apply_subtype (b := j) _ _ hj]
  rfl

lemma g72gk1_m_ext_symm_ge {M R : ℕ} (h : M ≤ R) (t : Equiv.Perm (Fin M)) (j : Fin R) (hj : ¬ j.val < M) :
    (g72gk1_m_ext h t).symm j = j := by
  have e : (g72gk1_m_ext h t).symm = g72gk1_m_ext h t⁻¹ := by
    rw [g72gk1_m_ext, g72gk1_m_ext, ← Equiv.Perm.extendDomain_inv]; rfl
  rw [e, g72gk1_m_ext, Equiv.Perm.extendDomain_apply_not_subtype (b := j) _ _ hj]

lemma g72gk1_m_tWI_tP {d M R : ℕ} (h : M ≤ R) (t : Equiv.Perm (Fin M)) :
    tensorWithIdentity h (Schur.tensorPermutation d M t) =
      Schur.tensorPermutation d R (g72gk1_m_ext h t) := by
  ext x y
  rw [g72gk1_m_tWI_apply]
  simp only [Schur.tensorPermutation, Matrix.of_apply, ite_zero_mul_ite_zero, mul_one]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    funext j
    simp only [Function.comp_apply]
    by_cases hj : j.val < M
    · rw [g72gk1_m_ext_symm_lt h t j hj]
      have := congrFun h1 ⟨j.val, hj⟩
      simpa using this
    · rw [g72gk1_m_ext_symm_ge h t j hj]; exact h2 j (by omega)
  · intro H
    refine ⟨?_, fun j hj => ?_⟩
    · funext k
      have := congrFun H ⟨k.val, by omega⟩
      simp only [Function.comp_apply] at this ⊢
      rw [this, g72gk1_m_ext_symm_lt h t _ k.2]
    · have := congrFun H j
      simp only [Function.comp_apply] at this
      rw [this, g72gk1_m_ext_symm_ge h t j (by omega)]

lemma g72gk1_m_absorb_l {d M R : ℕ} (h : M ≤ R) :
    boseProjector d R * tensorWithIdentity h (boseProjector d M) = boseProjector d R := by
  rw [show boseProjector d M = ((Fintype.card (Equiv.Perm (Fin M)) : ℂ)⁻¹) •
      ∑ p, Schur.tensorPermutation d M p from rfl, g72gk1_m_tWI_smul, g72gk1_m_tWI_sum, Matrix.mul_smul, Finset.mul_sum]
  simp only [g72gk1_m_tWI_tP, g72gk1_m_P_tP, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin M))).ne'), one_smul]

lemma g72gk1_m_absorb_r {d M R : ℕ} (h : M ≤ R) :
    tensorWithIdentity h (boseProjector d M) * boseProjector d R = boseProjector d R := by
  rw [show boseProjector d M = ((Fintype.card (Equiv.Perm (Fin M)) : ℂ)⁻¹) •
      ∑ p, Schur.tensorPermutation d M p from rfl, g72gk1_m_tWI_smul, g72gk1_m_tWI_sum, Matrix.smul_mul, Finset.sum_mul]
  simp only [g72gk1_m_tWI_tP, g72gk1_m_tP_P, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin M))).ne'), one_smul]

lemma g72gk1_m_boseDim_pos (d M : ℕ) (hd : 0 < d) : 0 < boseDimension d M := by
  unfold boseDimension; exact Nat.choose_pos (by omega)

/-- Part (a) of canonical_concatenation. -/
lemma g72gk1_m_concat (d N M R : ℕ) (hd : 0 < d) (hNM : N ≤ M) (hMR : M ≤ R) :
    (canonicalCloner (d := d) hMR ∘ canonicalCloner hNM) = canonicalCloner (hNM.trans hMR) := by
  funext A
  simp only [Function.comp_apply, canonicalCloner]
  set W := tensorWithIdentity hNM (boseProjector d N * A * boseProjector d N)
  set c1 : ℂ := (boseDimension d N : ℂ) / (boseDimension d M : ℂ)
  have h1 : boseProjector d M * (c1 • (boseProjector d M * W * boseProjector d M)) * boseProjector d M =
      c1 • (boseProjector d M * W * boseProjector d M) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]; congr 1
    simp only [← Matrix.mul_assoc, g72gk1_m_PP]
    simp only [Matrix.mul_assoc, g72gk1_m_PP]
  rw [h1, g72gk1_m_tWI_smul, g72gk1_m_tWI_mul, g72gk1_m_tWI_mul, g72gk1_m_tWI_tWI, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul]
  have hM : (boseDimension d M : ℂ) ≠ 0 := by exact_mod_cast (g72gk1_m_boseDim_pos d M hd).ne'
  have hc : (boseDimension d M : ℂ) / (boseDimension d R : ℂ) * c1 =
      (boseDimension d N : ℂ) / (boseDimension d R : ℂ) := by
    simp only [c1]; field_simp
  rw [hc]; congr 1
  simp only [← Matrix.mul_assoc, g72gk1_m_absorb_l]
  simp only [Matrix.mul_assoc, g72gk1_m_absorb_r]

/-- Part (b) of canonical_concatenation. -/
lemma g72gk1_m_coef (d N M : ℕ) (hNM : N < M) :
    canonicalCoefficient d N M = coefficientFactor d N / coefficientFactor d M := by
  unfold canonicalCoefficient coefficientFactor
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hdM : (0 : ℝ) < d + M := by positivity
  field_simp

/-! ### g68o: site reductions and Bose invariance -/

lemma g72gk1_o_tPA {d n : ℕ} (σ : Equiv.Perm (Fin n)) (A : TensorMat d n) (x y : Word n d) :
    (Schur.tensorPermutation d n σ * A) x y = A (x ∘ σ) y := by
  simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (x ∘ σ)]
  · rw [if_pos (by ext k; simp)]
  · intro b _ hb; rw [if_neg]; intro h; apply hb; rw [h]; ext k; simp
  · simp

lemma g72gk1_o_AtP {d n : ℕ} (σ : Equiv.Perm (Fin n)) (A : TensorMat d n) (x y : Word n d) :
    (A * Schur.tensorPermutation d n σ) x y = A x (y ∘ σ.symm) := by
  simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (y ∘ σ.symm)]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg hb]
  · simp

lemma g72gk1_o_linv {d n : ℕ} {A : TensorMat d n} (h : boseProjector d n * A = A)
    (σ : Equiv.Perm (Fin n)) (x y : Word n d) : A (x ∘ σ) y = A x y := by
  have h1 : Schur.tensorPermutation d n σ * A = A := by
    rw [← h, ← Matrix.mul_assoc, g72gk1_m_tP_P]
  rw [← g72gk1_o_tPA σ A x y, h1]

lemma g72gk1_o_rinv {d n : ℕ} {A : TensorMat d n} (h : A * boseProjector d n = A)
    (σ : Equiv.Perm (Fin n)) (x y : Word n d) : A x (y ∘ σ) = A x y := by
  have h1 : A * Schur.tensorPermutation d n σ.symm = A := by
    rw [← h, Matrix.mul_assoc, g72gk1_m_P_tP]
  have := g72gk1_o_AtP σ.symm A x y
  rw [h1, Equiv.symm_symm] at this
  exact this.symm

/-- site reduction in update form -/
def g72gk1_o_R {d n : ℕ} (i : Fin n) (X : TensorMat d n) : Matrix (Fin d) (Fin d) ℂ :=
  fun a b => ∑ x : Word n d, if x i = a then X x (Function.update x i b) else 0

def g72gk1_o_pe {d n : ℕ} (σ : Equiv.Perm (Fin n)) : Word n d ≃ Word n d where
  toFun y := y ∘ σ
  invFun y := y ∘ σ.symm
  left_inv y := by ext; simp
  right_inv y := by ext; simp

lemma g72gk1_o_R_swap {d n : ℕ} {X : TensorMat d n}
    (hX : ∀ σ : Equiv.Perm (Fin n), ∀ x y, X (x ∘ σ) (y ∘ σ) = X x y) (i j : Fin n) :
    g72gk1_o_R i X = g72gk1_o_R j X := by
  ext a b
  unfold g72gk1_o_R
  rw [← (g72gk1_o_pe (d := d) (Equiv.swap i j)).sum_comp]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp only [g72gk1_o_pe, Equiv.coe_fn_mk, Function.comp_apply, Equiv.swap_apply_left]
  congr 1
  have : Function.update (y ∘ Equiv.swap i j) i b = Function.update y j b ∘ Equiv.swap i j := by
    have := Function.update_comp_equiv y (Equiv.swap i j) j b
    rw [Equiv.symm_swap, Equiv.swap_apply_right] at this
    exact this.symm
  rw [this, hX]

lemma g72gk1_o_K {d n : ℕ} (i : Fin n) (G : Word n d → ℂ) (f : Word n d → Fin d)
    (hG : ∀ w c, G (Function.update w i c) = G w) (hf : ∀ w c, f (Function.update w i c) = f w)
    (a : Fin d) :
    (∑ w : Word n d, if w i = f w then G w else 0) = ∑ w : Word n d, if w i = a then G w else 0 := by
  let e : Word n d → Word n d := fun w => Function.update w i (Equiv.swap (f w) a (w i))
  have he : Function.Involutive e := by
    intro w
    simp only [e, hf, Function.update_self, Function.update_idem, Equiv.swap_apply_self,
      Function.update_eq_self]
  rw [← Equiv.sum_comp (he.toPerm e)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [Function.Involutive.coe_toPerm, e, Function.update_self, hG, hf]
  congr 1
  apply propext
  rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

lemma g72gk1_o_K_all {d n : ℕ} (i : Fin n) (G : Word n d → ℂ)
    (hG : ∀ w c, G (Function.update w i c) = G w) (a : Fin d) :
    (∑ w : Word n d, G w) = (d : ℂ) * ∑ w : Word n d, if w i = a then G w else 0 := by
  have : (∑ w : Word n d, G w) = ∑ c : Fin d, ∑ w : Word n d, if w i = c then G w else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.sum_ite_eq]; simp
  rw [this]
  have h2 : ∀ c : Fin d, (∑ w : Word n d, if w i = c then G w else 0) =
      ∑ w : Word n d, if w i = a then G w else 0 := fun c =>
    g72gk1_o_K i G (fun _ => c) hG (fun _ _ => rfl) a
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

def g72gk1_o_pre {d n : ℕ} (hn : 1 ≤ n) : Fin d × Word (n - 1) d ≃ Word n d where
  toFun p := prependWord hn p.1 p.2
  invFun x := (x ⟨0, by omega⟩, fun k => x ⟨k.val + 1, by omega⟩)
  left_inv p := by
    ext k
    · simp [prependWord]
    · simp [prependWord]
  right_inv x := by
    funext k
    by_cases hk : k.val = 0
    · simp only [prependWord, dif_pos hk]; congr 1; ext; simp [hk]
    · simp only [prependWord, dif_neg hk]; congr 1; ext; simp; omega

lemma g72gk1_o_oneSite_R {d n : ℕ} (hn : 1 ≤ n) (X : TensorMat d n) :
    oneSite hn X = g72gk1_o_R ⟨0, by omega⟩ X := by
  ext a b
  unfold oneSite g72gk1_o_R
  rw [← (g72gk1_o_pre (d := d) hn).sum_comp, Fintype.sum_prod_type]
  simp only [g72gk1_o_pre, Equiv.coe_fn_mk]
  have h1 : ∀ (c : Fin d) (z : Word (n - 1) d), prependWord hn c z ⟨0, by omega⟩ = c := by intro c z; simp [prependWord]
  have h2 : ∀ (c : Fin d) z, Function.update (prependWord hn c z) ⟨0, by omega⟩ b = prependWord hn b z := by
    intro c z; funext k
    by_cases hk : k.val = 0
    · have : k = ⟨0, by omega⟩ := Fin.ext hk
      rw [this]; simp [prependWord]
    · rw [Function.update_of_ne (by intro h; apply hk; rw [h])]
      simp [prependWord, hk]
  simp only [h1, h2]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq']

lemma g72gk1_o_trace_R {d n : ℕ} (i : Fin n) (X : TensorMat d n) :
    (g72gk1_o_R i X).trace = X.trace := by
  unfold g72gk1_o_R Matrix.trace
  simp only [Matrix.diag]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_ite_eq]; simp

lemma g72gk1_o_trace_oneSite {d n : ℕ} (hn : 1 ≤ n) (X : TensorMat d n) :
    (oneSite hn X).trace = X.trace := by
  rw [g72gk1_o_oneSite_R, g72gk1_o_trace_R]

/-! ### g68o: coset decomposition of the Bose projector -/

lemma g72gk1_o_ext_last (N : ℕ) (π : Equiv.Perm (Fin N)) :
    g72gk1_m_ext (Nat.le_succ N) π (Fin.last N) = Fin.last N := by
  have := g72gk1_m_ext_symm_ge (Nat.le_succ N) π (Fin.last N) (by simp)
  exact ((Equiv.symm_apply_eq _).mp this).symm

lemma g72gk1_o_ext_inj (N : ℕ) {π π' : Equiv.Perm (Fin N)}
    (h : g72gk1_m_ext (Nat.le_succ N) π = g72gk1_m_ext (Nat.le_succ N) π') : π = π' :=
  Equiv.Perm.extendDomainHom_injective (g72gk1_m_emb (Nat.le_succ N)) h

lemma g72gk1_o_card (N : ℕ) : Fintype.card (Fin (N+1) × Equiv.Perm (Fin N)) =
    Fintype.card (Equiv.Perm (Fin (N+1))) := by
  simp [Fintype.card_perm, Nat.factorial_succ]

lemma g72gk1_o_phi_bij (N : ℕ) : Function.Bijective
    (fun p : Fin (N+1) × Equiv.Perm (Fin N) => Equiv.swap p.1 (Fin.last N) * g72gk1_m_ext (Nat.le_succ N) p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, g72gk1_o_card N⟩
  rintro ⟨k, π⟩ ⟨k', π'⟩ h
  simp only at h
  have hk : k = k' := by
    have := congrArg (fun σ : Equiv.Perm (Fin (N+1)) => σ (Fin.last N)) h
    simpa [Equiv.Perm.mul_apply, g72gk1_o_ext_last] using this
  subst hk
  rw [g72gk1_o_ext_inj N (mul_left_cancel h)]

lemma g72gk1_o_psi_bij (N : ℕ) : Function.Bijective
    (fun p : Fin (N+1) × Equiv.Perm (Fin N) => g72gk1_m_ext (Nat.le_succ N) p.2 * Equiv.swap p.1 (Fin.last N)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, g72gk1_o_card N⟩
  rintro ⟨k, π⟩ ⟨k', π'⟩ h
  simp only at h
  have hk : k = k' := by
    have h1 : (g72gk1_m_ext (Nat.le_succ N) π * Equiv.swap k (Fin.last N)) k = Fin.last N := by
      simp [Equiv.Perm.mul_apply, g72gk1_o_ext_last]
    have h2 : (g72gk1_m_ext (Nat.le_succ N) π * Equiv.swap k (Fin.last N)) k' = Fin.last N := by
      rw [h]; simp [Equiv.Perm.mul_apply, g72gk1_o_ext_last]
    exact (g72gk1_m_ext (Nat.le_succ N) π * Equiv.swap k (Fin.last N)).injective (h1.trans h2.symm)
  subst hk
  rw [g72gk1_o_ext_inj N (mul_right_cancel h)]

lemma g72gk1_o_sumP (d N : ℕ) : ∑ π : Equiv.Perm (Fin N), Schur.tensorPermutation d (N+1) (g72gk1_m_ext (Nat.le_succ N) π) =
    ((Nat.factorial N : ℕ) : ℂ) • tensorWithIdentity (Nat.le_succ N) (boseProjector d N) := by
  rw [show boseProjector d N = ((Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹) •
      ∑ p, Schur.tensorPermutation d N p from rfl, g72gk1_m_tWI_smul, g72gk1_m_tWI_sum, smul_smul]
  simp only [g72gk1_m_tWI_tP, Fintype.card_perm, Fintype.card_fin]
  rw [mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_pos N).ne'), one_smul]

lemma g72gk1_o_Pdec_l (d N : ℕ) : boseProjector d (N+1) = ((N + 1 : ℂ))⁻¹ •
    ∑ k : Fin (N+1), Schur.tensorPermutation d (N+1) (Equiv.swap k (Fin.last N)) *
      tensorWithIdentity (Nat.le_succ N) (boseProjector d N) := by
  rw [show boseProjector d (N+1) = ((Fintype.card (Equiv.Perm (Fin (N+1))) : ℂ)⁻¹) •
      ∑ p, Schur.tensorPermutation d (N+1) p from rfl]
  rw [← Fintype.sum_bijective _ (g72gk1_o_phi_bij N) (fun p => Schur.tensorPermutation d (N+1)
    (Equiv.swap p.1 (Fin.last N) * g72gk1_m_ext (Nat.le_succ N) p.2)) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [← g72gk1_m_tP_mul, ← Finset.mul_sum, g72gk1_o_sumP, Matrix.mul_smul, ← Finset.smul_sum, smul_smul]
  congr 1
  simp only [Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]
  have : ((Nat.factorial N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  push_cast
  field_simp

lemma g72gk1_o_Pdec_r (d N : ℕ) : boseProjector d (N+1) = ((N + 1 : ℂ))⁻¹ •
    ∑ k : Fin (N+1), tensorWithIdentity (Nat.le_succ N) (boseProjector d N) *
      Schur.tensorPermutation d (N+1) (Equiv.swap k (Fin.last N)) := by
  rw [show boseProjector d (N+1) = ((Fintype.card (Equiv.Perm (Fin (N+1))) : ℂ)⁻¹) •
      ∑ p, Schur.tensorPermutation d (N+1) p from rfl]
  rw [← Fintype.sum_bijective _ (g72gk1_o_psi_bij N) (fun p => Schur.tensorPermutation d (N+1)
    (g72gk1_m_ext (Nat.le_succ N) p.2 * Equiv.swap p.1 (Fin.last N))) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [← g72gk1_m_tP_mul, ← Finset.sum_mul, g72gk1_o_sumP, Matrix.smul_mul, ← Finset.smul_sum, smul_smul]
  congr 1
  simp only [Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]
  have : ((Nat.factorial N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  push_cast
  field_simp

lemma g72gk1_o_tPBtP {d n : ℕ} (s t : Equiv.Perm (Fin n)) (B : TensorMat d n) (x y : Word n d) :
    (Schur.tensorPermutation d n s * B * Schur.tensorPermutation d n t) x y = B (x ∘ s) (y ∘ t.symm) := by
  rw [g72gk1_o_AtP, g72gk1_o_tPA]

lemma g72gk1_o_X_entry {d N : ℕ} (A : TensorMat d N) (hL : boseProjector d N * A = A)
    (hR : A * boseProjector d N = A) (x y : Word (N+1) d) :
    (boseProjector d (N+1) * tensorWithIdentity (Nat.le_succ N) A * boseProjector d (N+1)) x y =
      ((N + 1 : ℂ))⁻¹ ^ 2 * ∑ k : Fin (N+1), ∑ l : Fin (N+1),
        tensorWithIdentity (Nat.le_succ N) A (x ∘ Equiv.swap k (Fin.last N)) (y ∘ Equiv.swap l (Fin.last N)) := by
  have hA' : tensorWithIdentity (Nat.le_succ N) (boseProjector d N) * tensorWithIdentity (Nat.le_succ N) A *
      tensorWithIdentity (Nat.le_succ N) (boseProjector d N) = tensorWithIdentity (Nat.le_succ N) A := by
    rw [← g72gk1_m_tWI_mul, ← g72gk1_m_tWI_mul, hL, hR]
  have key : boseProjector d (N+1) * tensorWithIdentity (Nat.le_succ N) A * boseProjector d (N+1) =
      ((N + 1 : ℂ))⁻¹ ^ 2 • ∑ k : Fin (N+1), ∑ l : Fin (N+1),
        Schur.tensorPermutation d (N+1) (Equiv.swap k (Fin.last N)) * tensorWithIdentity (Nat.le_succ N) A *
          Schur.tensorPermutation d (N+1) (Equiv.swap l (Fin.last N)) := by
    nth_rewrite 1 [g72gk1_o_Pdec_l]
    rw [g72gk1_o_Pdec_r]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Finset.mul_sum, smul_smul, Finset.smul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [sq]; congr 1
    calc _ = Schur.tensorPermutation d (N+1) (Equiv.swap k (Fin.last N)) *
          (tensorWithIdentity (Nat.le_succ N) (boseProjector d N) * tensorWithIdentity (Nat.le_succ N) A *
            tensorWithIdentity (Nat.le_succ N) (boseProjector d N)) *
          Schur.tensorPermutation d (N+1) (Equiv.swap l (Fin.last N)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hA']
  rw [key, Matrix.smul_apply, smul_eq_mul]
  congr 1
  simp only [Matrix.sum_apply, g72gk1_o_tPBtP, Equiv.symm_swap]

lemma g72gk1_o_snoc_last {d N : ℕ} (w : Word N d) (c : Fin d) :
    (Fin.snoc w c : Word (N+1) d) ∘ Equiv.swap (Fin.last N) (Fin.last N) = Fin.snoc w c := by
  rw [Equiv.swap_self]; rfl

lemma g72gk1_o_snoc_cs {d N : ℕ} (w : Word N d) (c : Fin d) (k : Fin N) :
    (Fin.snoc w c : Word (N+1) d) ∘ Equiv.swap k.castSucc (Fin.last N) =
      Fin.snoc (Function.update w k c) (w k) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · simp only [Function.comp_apply]
    by_cases hik : i = k
    · subst hik; simp
    · rw [Equiv.swap_apply_of_ne_of_ne (by simpa using hik) (Fin.castSucc_ne_last i)]
      simp [Function.update_of_ne hik]

lemma g72gk1_o_tWI_snoc {d N : ℕ} (A : TensorMat d N) (u v : Word N d) (c c' : Fin d) :
    tensorWithIdentity (Nat.le_succ N) A (Fin.snoc u c : Word (N+1) d) (Fin.snoc v c') =
      A u v * if c = c' then 1 else 0 := by
  rw [g72gk1_m_tWI_apply]
  have e1 : ∀ z : Word N d, ∀ c0 : Fin d,
      (fun k : Fin N => (Fin.snoc z c0 : Word (N+1) d) ⟨k.val, by omega⟩) = z := by
    intro z c0; funext k
    exact Fin.snoc_castSucc (α := fun _ => Fin d) (p := z) (x := c0) (i := k)
  rw [e1, e1]
  congr 2
  apply propext
  constructor
  · intro H; have := H (Fin.last N) (by simp); simpa using this
  · intro H j hj
    have : j = Fin.last N := Fin.ext (by have := j.isLt; simp; omega)
    subst this; simpa using H

/-! ### g68o: one-step reduction -/

lemma g72gk1_o_hX {d n : ℕ} {A : TensorMat d n} (hL : boseProjector d n * A = A)
    (hR : A * boseProjector d n = A) :
    ∀ σ : Equiv.Perm (Fin n), ∀ x y, A (x ∘ σ) (y ∘ σ) = A x y := by
  intro σ x y; rw [g72gk1_o_linv hL, g72gk1_o_rinv hR]

lemma g72gk1_o_Rlast_snoc {d N : ℕ} (X : TensorMat d (N+1)) (a b : Fin d) :
    g72gk1_o_R (Fin.last N) X a b = ∑ w : Word N d, X (Fin.snoc w a) (Fin.snoc w b) := by
  unfold g72gk1_o_R
  rw [← (Fin.snocEquiv (fun _ => Fin d)).sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    simp [Fin.snocEquiv, Fin.update_snoc_last]
  · intro c _ hc
    refine Finset.sum_eq_zero (fun w _ => ?_)
    simp [Fin.snocEquiv, hc]
  · simp

lemma g72gk1_o_Llc {d N : ℕ} (hN : 1 ≤ N) {A : TensorMat d N} (hL : boseProjector d N * A = A)
    (hR : A * boseProjector d N = A) (a b : Fin d) :
    (∑ w : Word N d, ∑ j : Fin N, A w (Function.update w j b) * (if a = w j then 1 else 0)) =
      (N : ℂ) * g72gk1_o_R ⟨0, by omega⟩ A a b := by
  rw [Finset.sum_comm]
  have : ∀ j : Fin N, (∑ w : Word N d, A w (Function.update w j b) * (if a = w j then 1 else 0)) =
      g72gk1_o_R ⟨0, by omega⟩ A a b := by
    intro j
    rw [← g72gk1_o_R_swap (g72gk1_o_hX hL hR) j]
    unfold g72gk1_o_R
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases h : w j = a
    · rw [if_pos h.symm, if_pos h, mul_one]
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma g72gk1_o_Lcl {d N : ℕ} (hN : 1 ≤ N) {A : TensorMat d N} (hL : boseProjector d N * A = A)
    (hR : A * boseProjector d N = A) (a b : Fin d) :
    (∑ w : Word N d, ∑ i : Fin N, A (Function.update w i a) w * (if w i = b then 1 else 0)) =
      (N : ℂ) * g72gk1_o_R ⟨0, by omega⟩ A a b := by
  rw [Finset.sum_comm]
  have : ∀ i : Fin N, (∑ w : Word N d, A (Function.update w i a) w * (if w i = b then 1 else 0)) =
      g72gk1_o_R ⟨0, by omega⟩ A a b := by
    intro i
    rw [← g72gk1_o_R_swap (g72gk1_o_hX hL hR) i]
    unfold g72gk1_o_R
    have e1 : ∀ w : Word N d, A (Function.update w i a) w * (if w i = b then 1 else 0) =
        if w i = (fun _ => b) w then A (Function.update w i a) (Function.update w i b) else 0 := by
      intro w
      by_cases h : w i = b
      · rw [if_pos h, if_pos h, mul_one]; congr 1; rw [← h, Function.update_eq_self]
      · rw [if_neg h, if_neg h, mul_zero]
    simp only [e1]
    rw [g72gk1_o_K i (fun w => A (Function.update w i a) (Function.update w i b)) (fun _ => b)
      (fun w c => by simp only [Function.update_idem]) (fun _ _ => rfl) a]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases h : w i = a
    · rw [if_pos h, if_pos h]; congr 1; rw [← h, Function.update_eq_self]
    · rw [if_neg h, if_neg h]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma g72gk1_o_Lcc {d N : ℕ} (hN : 1 ≤ N) {A : TensorMat d N} (hL : boseProjector d N * A = A)
    (hR : A * boseProjector d N = A) (a b : Fin d) :
    (∑ w : Word N d, ∑ i : Fin N, ∑ j : Fin N,
      A (Function.update w i a) (Function.update w j b) * (if w i = w j then 1 else 0)) =
      (N : ℂ) * ((N : ℂ) + d - 1) * g72gk1_o_R ⟨0, by omega⟩ A a b := by
  set Q := g72gk1_o_R ⟨0, by omega⟩ A a b
  have hX := g72gk1_o_hX hL hR
  rw [Finset.sum_comm]
  have hi : ∀ i : Fin N, (∑ w : Word N d, ∑ j : Fin N,
      A (Function.update w i a) (Function.update w j b) * (if w i = w j then 1 else 0)) =
      (N : ℂ) * Q + ((d : ℂ) - 1) * Q := by
    intro i
    rw [Finset.sum_comm]
    have hG : ∀ (w : Word N d) (c : Fin d), (fun w => A (Function.update w i a) (Function.update w i b))
        (Function.update w i c) = (fun w => A (Function.update w i a) (Function.update w i b)) w := by
      intro w c; simp only [Function.update_idem]
    have hRi : (∑ w : Word N d, if w i = a then A (Function.update w i a) (Function.update w i b) else 0) = Q := by
      show _ = g72gk1_o_R ⟨0, by omega⟩ A a b
      rw [← g72gk1_o_R_swap hX i]
      unfold g72gk1_o_R
      refine Finset.sum_congr rfl (fun w _ => ?_)
      by_cases h : w i = a
      · rw [if_pos h, if_pos h]; congr 1; rw [← h, Function.update_eq_self]
      · rw [if_neg h, if_neg h]
    have hj : ∀ j : Fin N, (∑ w : Word N d,
        A (Function.update w i a) (Function.update w j b) * (if w i = w j then 1 else 0)) =
        Q + (if i = j then ((d : ℂ) - 1) * Q else 0) := by
      intro j
      by_cases hij : i = j
      · subst hij
        simp only [if_true, mul_one]
        rw [g72gk1_o_K_all i _ hG a, hRi]; ring
      · rw [if_neg hij, add_zero]
        have e1 : ∀ w : Word N d, A (Function.update w i a) (Function.update w j b) *
            (if w i = w j then 1 else 0) =
            if w i = (fun w : Word N d => w j) w then A (Function.update w i a) (Function.update w i b) else 0 := by
          intro w
          by_cases h : w i = w j
          · rw [if_pos h, if_pos h, mul_one]
            have hw : w ∘ Equiv.swap i j = w := by
              funext k; simp only [Function.comp_apply]
              by_cases hk1 : k = i
              · subst hk1; rw [Equiv.swap_apply_left, h]
              · by_cases hk2 : k = j
                · subst hk2; rw [Equiv.swap_apply_right, h]
                · rw [Equiv.swap_apply_of_ne_of_ne hk1 hk2]
            have hu : Function.update w j b ∘ Equiv.swap i j = Function.update w i b := by
              have := Function.update_comp_equiv w (Equiv.swap i j) j b
              rw [Equiv.symm_swap, Equiv.swap_apply_right, hw] at this
              exact this
            rw [← hu, g72gk1_o_rinv hR]
          · rw [if_neg h, if_neg h, mul_zero]
        simp only [e1]
        rw [g72gk1_o_K i _ (fun w : Word N d => w j) hG
          (fun w c => by simp [Function.update_of_ne (Ne.symm hij)]) a, hRi]
    simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma g72gk1_o_Rlast {d N : ℕ} (hN : 1 ≤ N) (A : TensorMat d N) (hL : boseProjector d N * A = A)
    (hR : A * boseProjector d N = A) (a b : Fin d) :
    g72gk1_o_R (Fin.last N) (boseProjector d (N+1) * tensorWithIdentity (Nat.le_succ N) A *
      boseProjector d (N+1)) a b =
      ((N + 1 : ℂ))⁻¹ ^ 2 * ((if a = b then 1 else 0) * A.trace +
        (N : ℂ) * ((N : ℂ) + d + 1) * g72gk1_o_R ⟨0, by omega⟩ A a b) := by
  rw [g72gk1_o_Rlast_snoc]
  simp only [g72gk1_o_X_entry A hL hR, Fin.sum_univ_castSucc, g72gk1_o_snoc_cs, g72gk1_o_snoc_last, g72gk1_o_tWI_snoc]
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_add_distrib]
  rw [g72gk1_o_Lcc hN hL hR, g72gk1_o_Lcl hN hL hR, g72gk1_o_Llc hN hL hR]
  have : (∑ w : Word N d, A w w * (if a = b then 1 else 0)) = (if a = b then 1 else 0) * A.trace := by
    rw [Matrix.trace, ← Finset.sum_mul, mul_comm]; rfl
  rw [this]; ring

/-! ### g68o: Black Cow coefficient of the canonical cloner -/

lemma g72gk1_o_oneSite_smul {d n : ℕ} (hn : 1 ≤ n) (c : ℂ) (X : TensorMat d n) :
    oneSite hn (c • X) = c • oneSite hn X := by
  ext a b; simp [oneSite, Finset.mul_sum]

lemma g72gk1_o_bD_succ (d N : ℕ) (hd : 0 < d) :
    ((boseDimension d (N+1) : ℕ) : ℂ) * ((N : ℂ) + 1) = (boseDimension d N : ℂ) * ((d : ℂ) + N) := by
  unfold boseDimension
  have h := Nat.add_one_mul_choose_eq (d + N - 1) N
  have e1 : d + N - 1 + 1 = d + N := by omega
  have e2 : d + (N + 1) - 1 = d + N := by omega
  rw [e1] at h; rw [e2]
  have h' : ((d + N : ℕ) : ℂ) * ((d + N - 1).choose N : ℂ) = ((d + N).choose (N + 1) : ℂ) * ((N + 1 : ℕ) : ℂ) := by
    exact_mod_cast h
  push_cast at h'
  linear_combination -h'

lemma g72gk1_o_bose_out {d N M : ℕ} (h : N ≤ M) (A : TensorMat d N) :
    BoseSupported (canonicalCloner (d := d) h A) := by
  unfold canonicalCloner BoseSupported
  constructor
  · rw [Matrix.mul_smul]; congr 1; simp only [← Matrix.mul_assoc, g72gk1_m_PP]
  · rw [Matrix.smul_mul]; congr 1; simp only [Matrix.mul_assoc, g72gk1_m_PP]

lemma g72gk1_o_trace_oneMixed (d : ℕ) (hd : 0 < d) : (oneMixed d).trace = 1 := by
  unfold oneMixed
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

lemma g72gk1_o_bc_trace {d N M : ℕ} (hd : 0 < d) (hN : 1 ≤ N) (hM : 1 ≤ M) (T : CloneMap d N M) (g : ℝ)
    (hT : HasBlackCowCoefficient hN hM T g) (A : TensorMat d N) (hA : BoseSupported A) :
    (T A).trace = A.trace := by
  have := congrArg Matrix.trace (hT A hA)
  rw [g72gk1_o_trace_oneSite, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, g72gk1_o_trace_oneSite,
    g72gk1_o_trace_oneMixed d hd] at this
  rw [this]; simp only [smul_eq_mul]; push_cast; ring

lemma g72gk1_o_bc_comp {d N M R : ℕ} (hd : 0 < d) (hN : 1 ≤ N) (hM : 1 ≤ M) (hR : 1 ≤ R)
    (T : CloneMap d N M) (S : CloneMap d M R) (g1 g2 : ℝ)
    (hT : HasBlackCowCoefficient hN hM T g1) (hS : HasBlackCowCoefficient hM hR S g2)
    (hTB : ∀ A, BoseSupported A → BoseSupported (T A)) :
    HasBlackCowCoefficient hN hR (S ∘ T) (g2 * g1) := by
  intro A hA
  simp only [Function.comp_apply]
  rw [hS (T A) (hTB A hA), hT A hA, g72gk1_o_bc_trace hd hN hM T g1 hT A hA]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast; ring

lemma g72gk1_o_tWI_self {d N : ℕ} (h : N ≤ N) (A : TensorMat d N) : tensorWithIdentity h A = A := by
  ext x y
  rw [g72gk1_m_tWI_apply]
  have : (∀ j : Fin N, N ≤ j.val → x j = y j) := fun j hj => absurd j.isLt (by omega)
  rw [if_pos this, mul_one]

lemma g72gk1_o_bc_base {d N : ℕ} (hN : 1 ≤ N) (hd : 0 < d) :
    HasBlackCowCoefficient hN hN (canonicalCloner (d := d) (le_refl N)) 1 := by
  intro A hA
  have hc : canonicalCloner (d := d) (le_refl N) A = A := by
    unfold canonicalCloner
    rw [g72gk1_o_tWI_self, hA.1, hA.2, hA.1, hA.2, div_self, one_smul]
    exact_mod_cast (g72gk1_m_boseDim_pos d N hd).ne'
  rw [hc]; simp

lemma g72gk1_o_bc_step {d N : ℕ} (hd : 0 < d) (hN : 1 ≤ N) :
    HasBlackCowCoefficient hN (by omega : 1 ≤ N + 1) (canonicalCloner (d := d) (Nat.le_succ N))
      (coefficientFactor d N / coefficientFactor d (N+1)) := by
  intro A hA
  have hL := hA.1
  have hR := hA.2
  have hPAP : boseProjector d N * A * boseProjector d N = A := by rw [hL, hR]
  unfold canonicalCloner
  rw [hPAP, g72gk1_o_oneSite_smul]
  set X := boseProjector d (N+1) * tensorWithIdentity (Nat.le_succ N) A * boseProjector d (N+1) with hXdef
  have hXL : boseProjector d (N+1) * X = X := by simp only [hXdef, ← Matrix.mul_assoc, g72gk1_m_PP]
  have hXR : X * boseProjector d (N+1) = X := by simp only [hXdef, Matrix.mul_assoc, g72gk1_m_PP]
  rw [g72gk1_o_oneSite_R, g72gk1_o_R_swap (g72gk1_o_hX hXL hXR) _ (Fin.last N), g72gk1_o_oneSite_R hN]
  ext a b
  rw [Matrix.smul_apply, hXdef, g72gk1_o_Rlast hN A hL hR a b]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, oneMixed, Matrix.one_apply]
  have hb := g72gk1_o_bD_succ d N hd
  have hbN : (boseDimension d N : ℂ) ≠ 0 := by exact_mod_cast (g72gk1_m_boseDim_pos d N hd).ne'
  have hbN1 : (boseDimension d (N+1) : ℂ) ≠ 0 := by exact_mod_cast (g72gk1_m_boseDim_pos d (N+1) hd).ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hN1 : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (show N + 1 ≠ 0 by omega)
  have hdN : (d : ℂ) + N ≠ 0 := by exact_mod_cast (show d + N ≠ 0 by omega)
  have hdN1 : (d : ℂ) + (N + 1) ≠ 0 := by exact_mod_cast (show d + (N + 1) ≠ 0 by omega)
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hc : (boseDimension d N : ℂ) / (boseDimension d (N+1) : ℂ) = ((N : ℂ) + 1) / ((d : ℂ) + N) := by
    rw [div_eq_div_iff hbN1 hdN]; linear_combination -hb
  rw [hc]
  unfold coefficientFactor
  push_cast
  split_ifs <;> field_simp <;> ring

lemma g72gk1_o_bc_all {d N : ℕ} (hd : 0 < d) (hN : 1 ≤ N) :
    ∀ M (h : N ≤ M), HasBlackCowCoefficient hN (by omega : 1 ≤ M) (canonicalCloner (d := d) h)
      (coefficientFactor d N / coefficientFactor d M) := by
  intro M h
  induction M, h using Nat.le_induction with
  | base =>
    have hf : coefficientFactor d N ≠ 0 := by
      unfold coefficientFactor
      have : (0 : ℝ) < N := by exact_mod_cast hN
      positivity
    rw [div_self hf]; exact g72gk1_o_bc_base hN hd
  | succ M hNM ih =>
    have hcomp := g72gk1_m_concat d N M (M+1) hd hNM (Nat.le_succ M)
    rw [← hcomp]
    have hfM : coefficientFactor d M ≠ 0 := by
      unfold coefficientFactor
      have : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      positivity
    have := g72gk1_o_bc_comp hd hN (by omega) (by omega) _ _ _ _ ih (g72gk1_o_bc_step hd (show 1 ≤ M by omega))
      (fun A _ => g72gk1_o_bose_out hNM A)
    convert this using 1
    field_simp
lemma g72gk1_j_pvc {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (x : Word n d) :
    coherentTensor n phi x = ∏ k, phi (x k) := rfl

lemma g72gk1_j_PD {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
    boseProjector d n * pureDensity (coherentTensor n phi) = pureDensity (coherentTensor n phi) := by
  have hp : ∀ p : Equiv.Perm (Fin n),
      Schur.tensorPermutation d n p * pureDensity (coherentTensor n phi) =
        pureDensity (coherentTensor n phi) := by
    intro p
    ext y z
    simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, pureDensity, ite_mul,
      one_mul, zero_mul]
    rw [Finset.sum_eq_single (y ∘ p)]
    · rw [if_pos (by ext k; simp)]
      congr 1
      simp only [g72gk1_j_pvc, Function.comp_apply]
      exact Equiv.prod_comp p (fun k => phi (y k))
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; rw [h]; ext k; simp
    · simp
  rw [boseProjector, Matrix.smul_mul, Finset.sum_mul]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin n))).ne'), one_smul]

lemma g72gk1_j_DP {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
    pureDensity (coherentTensor n phi) * boseProjector d n = pureDensity (coherentTensor n phi) := by
  have hp : ∀ p : Equiv.Perm (Fin n),
      pureDensity (coherentTensor n phi) * Schur.tensorPermutation d n p =
        pureDensity (coherentTensor n phi) := by
    intro p
    ext y z
    simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, pureDensity, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_eq_single (z ∘ p.symm)]
    · rw [if_pos rfl]
      congr 2
      simp only [g72gk1_j_pvc, Function.comp_apply]
      exact Equiv.prod_comp p.symm (fun k => phi (z k))
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; rw [h]
    · simp
  rw [boseProjector, Matrix.mul_smul, Finset.mul_sum]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin n))).ne'), one_smul]
lemma g72gk1_j_norm1 {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    ∑ u : Word n d, coherentTensor n phi u * conj (coherentTensor n phi u) = 1 := by
  simp only [g72gk1_j_pvc, map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin n) a => phi a * conj (phi a))]
  have : ∑ a, phi a * conj (phi a) = 1 := by
    have h2 : ‖phi‖ ^ 2 = 1 := by rw [hphi]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h2
    simp only [Complex.mul_conj']
    exact_mod_cast h2
  simp [this]

lemma g72gk1_o_coh_bose {d N : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
    BoseSupported (pureDensity (coherentTensor N phi)) := ⟨g72gk1_j_PD phi, g72gk1_j_DP phi⟩

lemma g72gk1_o_coh_trace {d N : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    (pureDensity (coherentTensor N phi)).trace = 1 := by
  rw [← g72gk1_j_norm1 (n := N) phi hphi]; rfl

lemma g72gk1_o_coh_oneSite {d N : ℕ} (hN : 1 ≤ N) (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    oneSite hN (pureDensity (coherentTensor N phi)) = pureDensity phi := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hv : ∀ (a : Fin d) (z : Word (n + 1 - 1) d),
      coherentTensor (n+1) phi (prependWord hN a z) = phi a * coherentTensor n phi z := by
    intro a z
    rw [g72gk1_j_pvc, g72gk1_j_pvc, Fin.prod_univ_succ]
    congr 1
  ext a b
  simp only [oneSite, pureDensity, Matrix.of_apply, hv, map_mul]
  have := g72gk1_j_norm1 (n := n) phi hphi
  calc _ = phi a * conj (phi b) * ∑ z : Word n d, coherentTensor n phi z * conj (coherentTensor n phi z) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => by ring)
    _ = _ := by rw [this, mul_one]

lemma g72gk1_o_rho_trace {d : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    (pureDensity phi).trace = 1 := by
  have := g72gk1_j_norm1 (n := 1) phi hphi
  simp only [g72gk1_j_pvc, Finset.univ_unique, Finset.prod_singleton] at this
  rw [← this, Matrix.trace]
  simp only [Matrix.diag, pureDensity, Matrix.of_apply]
  exact (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin d)).symm _ _ (fun _ => rfl))

lemma g72gk1_o_rho_idem {d : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    pureDensity phi * pureDensity phi = pureDensity phi := by
  have ht := g72gk1_o_rho_trace phi hphi
  simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply] at ht
  ext a c
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply]
  calc _ = phi a * conj (phi c) * ∑ b, phi b * conj (phi b) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)
    _ = _ := by rw [ht, mul_one]

/-! ### g68o: canonical cloner is a covariant CP corner channel -/

open scoped Kronecker in
theorem g72gk1_o_kraus_cp {I J ι : Type*} [Fintype I] [Fintype J] (s : Finset ι)
    (K : ι → Matrix J I ℂ) (L : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hL : ∀ X, L X = ∑ t ∈ s, K t * X * (K t)ᴴ) : Entanglement.IsCompletelyPositive L := by
  classical
  intro r Y hY
  have h : idTensorSuperop L Y =
      ∑ t ∈ s, ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ K t) * Y * ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ K t)ᴴ := by
    ext p q
    rw [Matrix.sum_apply]
    simp only [idTensorSuperop, Matrix.of_apply, hL, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.one_apply, Matrix.of_apply, Finset.sum_mul]
    simp only [star_mul', ite_mul, one_mul, zero_mul, mul_ite, mul_zero, star_zero]
    simp only [apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  exact Matrix.posSemidef_sum _ (fun t _ => hY.mul_mul_conjTranspose_same _)

lemma g72gk1_o_tP_H {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Schur.tensorPermutation d n σ)ᴴ = Schur.tensorPermutation d n σ⁻¹ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, Schur.tensorPermutation, Matrix.of_apply]
  rw [apply_ite (star : ℂ → ℂ), star_one, star_zero]
  congr 1
  apply propext
  constructor
  · intro h; rw [h]; ext k; simp [Equiv.Perm.inv_def]
  · intro h; rw [h]; ext k; simp [Equiv.Perm.inv_def]

lemma g72gk1_o_P_H {d n : ℕ} : (boseProjector d n)ᴴ = boseProjector d n := by
  unfold boseProjector
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [g72gk1_o_tP_H]
  congr 1
  · simp
  · exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun _ => rfl)

def g72gk1_o_J {d N M : ℕ} (h : N ≤ M) (z : Word (M - N) d) : Matrix (Word M d) (Word N d) ℂ :=
  Matrix.of fun x u => if g72gk1_m_split h x = (u, z) then 1 else 0

lemma g72gk1_o_J_sum {d N M : ℕ} (h : N ≤ M) (B : Matrix (Word N d) (Word N d) ℂ) :
    ∑ z, (g72gk1_o_J h z : Matrix (Word M d) (Word N d) ℂ) * B * (g72gk1_o_J h z)ᴴ = tensorWithIdentity h B := by
  ext x y
  rw [Matrix.sum_apply, g72gk1_m_tWI_apply]
  have e : ∀ z, (g72gk1_o_J h z * B * (g72gk1_o_J h z)ᴴ) x y =
      if (g72gk1_m_split h x).2 = z ∧ (g72gk1_m_split h y).2 = z then
        B (g72gk1_m_split h x).1 (g72gk1_m_split h y).1 else 0 := by
    intro z
    rw [Matrix.mul_apply, Finset.sum_eq_single (g72gk1_m_split h y).1]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (g72gk1_m_split h x).1]
      · simp only [g72gk1_o_J, Matrix.of_apply, Matrix.conjTranspose_apply, Prod.ext_iff, true_and]
        split_ifs <;> simp_all
      · intro b _ hb; simp only [g72gk1_o_J, Matrix.of_apply, Prod.ext_iff]; rw [if_neg (by tauto)]; simp
      · simp
    · intro b _ hb; simp only [Matrix.conjTranspose_apply, g72gk1_o_J, Matrix.of_apply, Prod.ext_iff]
      rw [if_neg (by tauto)]; simp
    · simp
  simp only [e]
  have hs : (∑ z, if (g72gk1_m_split h x).2 = z ∧ (g72gk1_m_split h y).2 = z then
      B (g72gk1_m_split h x).1 (g72gk1_m_split h y).1 else 0) =
      if (g72gk1_m_split h x).2 = (g72gk1_m_split h y).2 then B (g72gk1_m_split h x).1 (g72gk1_m_split h y).1 else 0 := by
    by_cases hc : (g72gk1_m_split h x).2 = (g72gk1_m_split h y).2
    · rw [if_pos hc, Finset.sum_eq_single (g72gk1_m_split h x).2]
      · rw [if_pos ⟨rfl, hc.symm⟩]
      · intro b _ hb; rw [if_neg]; rintro ⟨h1, _⟩; exact hb h1.symm
      · simp
    · rw [if_neg hc]; apply Finset.sum_eq_zero; intro z _; rw [if_neg]
      rintro ⟨h1, h2⟩; exact hc (h1.trans h2.symm)
  rw [hs]
  have hiff : (g72gk1_m_split h x).2 = (g72gk1_m_split h y).2 ↔ ∀ j : Fin M, N ≤ j.val → x j = y j := by
    constructor
    · intro H j hj
      have := congrFun H ⟨j.val - N, by omega⟩
      simp only [g72gk1_m_split, Equiv.coe_fn_mk] at this
      convert this using 2 <;> ext <;> simp <;> omega
    · intro H; funext k; exact H _ (by simp)
  by_cases hc : (g72gk1_m_split h x).2 = (g72gk1_m_split h y).2
  · rw [if_pos hc, if_pos (hiff.1 hc), mul_one]; rfl
  · rw [if_neg hc, if_neg (fun H => hc (hiff.2 H)), mul_zero]

def g72gk1_o_Kr {d N M : ℕ} (h : N ≤ M) (z : Word (M - N) d) : Matrix (Word M d) (Word N d) ℂ :=
  ((Real.sqrt ((boseDimension d N : ℝ) / boseDimension d M) : ℝ) : ℂ) •
    ((boseProjector d M : Matrix (Word M d) (Word M d) ℂ) * g72gk1_o_J h z * boseProjector d N)

lemma g72gk1_o_kraus_eq {d N M : ℕ} (h : N ≤ M) (A : TensorMat d N) :
    canonicalCloner h A = ∑ z, (g72gk1_o_Kr h z : Matrix (Word M d) (Word N d) ℂ) * A * (g72gk1_o_Kr h z)ᴴ := by
  have hs : ((Real.sqrt ((boseDimension d N : ℝ) / boseDimension d M) : ℝ) : ℂ) *
      star ((Real.sqrt ((boseDimension d N : ℝ) / boseDimension d M) : ℝ) : ℂ) =
      (boseDimension d N : ℂ) / (boseDimension d M : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity)]
    push_cast; rfl
  unfold canonicalCloner
  simp only [g72gk1_o_Kr, Matrix.smul_mul, Matrix.mul_smul, Matrix.conjTranspose_smul, smul_smul,
    Matrix.conjTranspose_mul, g72gk1_o_P_H, ← Finset.smul_sum]
  rw [mul_comm, hs]
  congr 1
  rw [← g72gk1_o_J_sum h]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  simp only [Matrix.mul_assoc]

def g72gk1_o_Lmap {d N M : ℕ} (h : N ≤ M) : TensorMat d N →ₗ[ℂ] TensorMat d M where
  toFun A := ∑ z, (g72gk1_o_Kr h z : Matrix (Word M d) (Word N d) ℂ) * A * (g72gk1_o_Kr h z)ᴴ
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]

lemma g72gk1_o_cp {d N M : ℕ} (h : N ≤ M) : Entanglement.IsCompletelyPositive (g72gk1_o_Lmap (d := d) h) :=
  g72gk1_o_kraus_cp Finset.univ (g72gk1_o_Kr h) _ (fun _ => rfl)

/-! covariance -/

lemma g72gk1_o_pk_tP {d n : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (σ : Equiv.Perm (Fin n)) :
    piKron n U * Schur.tensorPermutation d n σ = Schur.tensorPermutation d n σ * piKron n U := by
  ext x y
  rw [g72gk1_o_AtP, g72gk1_o_tPA]
  simp only [piKron, Matrix.of_apply, Function.comp_apply]
  rw [← Equiv.prod_comp σ]
  simp

lemma g72gk1_o_pk_P {d n : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    piKron n U * boseProjector d n = boseProjector d n * piKron n U := by
  unfold boseProjector
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [g72gk1_o_pk_tP]

lemma g72gk1_o_pk_H {d n : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : (piKron n U)ᴴ = piKron n Uᴴ := by
  ext x y
  simp [piKron, Matrix.conjTranspose_apply]

lemma g72gk1_o_pk_mul {d n : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ) :
    piKron n U * piKron n V = piKron n (U * V) := by
  ext x y
  simp only [Matrix.mul_apply, piKron, Matrix.of_apply, ← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum (fun i c => U (x i) c * V c (y i))]

lemma g72gk1_o_pk_one {d n : ℕ} : piKron n (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra H; exact hxy (funext fun i => not_not.mp (fun hi => H ⟨i, hi⟩))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma g72gk1_o_pk_unit {d n : ℕ} (u : Matrix.unitaryGroup (Fin d) ℂ) :
    piKron n (u : Matrix (Fin d) (Fin d) ℂ) * (piKron n (u : Matrix (Fin d) (Fin d) ℂ))ᴴ = 1 := by
  rw [g72gk1_o_pk_H, g72gk1_o_pk_mul]
  have : (u : Matrix (Fin d) (Fin d) ℂ) * (u : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp u.2
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [this, g72gk1_o_pk_one]

lemma g72gk1_o_tWI_e {d N M : ℕ} (h : N ≤ M) (B : TensorMat d N) (x y : Word M d) :
    tensorWithIdentity h B x y = B (g72gk1_m_split h x).1 (g72gk1_m_split h y).1 *
      if (g72gk1_m_split h x).2 = (g72gk1_m_split h y).2 then 1 else 0 := by
  rw [g72gk1_m_tWI_apply]
  have hiff : (g72gk1_m_split h x).2 = (g72gk1_m_split h y).2 ↔ ∀ j : Fin M, N ≤ j.val → x j = y j := by
    constructor
    · intro H j hj
      have := congrFun H ⟨j.val - N, by omega⟩
      simp only [g72gk1_m_split, Equiv.coe_fn_mk] at this
      convert this using 2 <;> ext <;> simp <;> omega
    · intro H; funext k; exact H _ (by simp)
  rw [if_congr hiff rfl rfl]; rfl

open scoped Kronecker in
lemma g72gk1_o_tWI_sub {d N M : ℕ} (h : N ≤ M) (B : TensorMat d N) :
    (tensorWithIdentity h B).submatrix (g72gk1_m_split h).symm (g72gk1_m_split h).symm =
      B ⊗ₖ (1 : Matrix (Word (M - N) d) (Word (M - N) d) ℂ) := by
  ext p q
  rw [Matrix.submatrix_apply, g72gk1_o_tWI_e]
  simp only [Equiv.apply_symm_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]

open scoped Kronecker in
lemma g72gk1_o_pk_sub {d N M : ℕ} (h : N ≤ M) (U : Matrix (Fin d) (Fin d) ℂ) :
    (piKron M U).submatrix (g72gk1_m_split h).symm (g72gk1_m_split h).symm =
      piKron N U ⊗ₖ piKron (M - N) U := by
  have key : ∀ x y : Word M d, piKron M U x y =
      piKron N U (g72gk1_m_split h x).1 (g72gk1_m_split h y).1 *
        piKron (M - N) U (g72gk1_m_split h x).2 (g72gk1_m_split h y).2 := by
    intro x y
    simp only [piKron, Matrix.of_apply, g72gk1_m_split, Equiv.coe_fn_mk]
    have hM : N + (M - N) = M := by omega
    rw [← Fin.prod_congr' (fun j => U (x j) (y j)) hM, Fin.prod_univ_add]
    rfl
  ext p q
  rw [Matrix.submatrix_apply, key]
  simp only [Equiv.apply_symm_apply, Matrix.kroneckerMap_apply]

open scoped Kronecker in
lemma g72gk1_o_tWI_cov {d N M : ℕ} (h : N ≤ M) (u : Matrix.unitaryGroup (Fin d) ℂ) (B : TensorMat d N) :
    tensorWithIdentity h (piKron N (u : Matrix (Fin d) (Fin d) ℂ) * B * (piKron N (u : Matrix (Fin d) (Fin d) ℂ))ᴴ) =
      piKron M (u : Matrix (Fin d) (Fin d) ℂ) * tensorWithIdentity h B * (piKron M (u : Matrix (Fin d) (Fin d) ℂ))ᴴ := by
  set e := g72gk1_m_split (d := d) h
  have hinj : ∀ X Y : TensorMat d M, X.submatrix e.symm e.symm = Y.submatrix e.symm e.symm → X = Y := by
    intro X Y hXY
    have := congrArg (fun Z => Z.submatrix e e) hXY
    simpa [Matrix.submatrix_submatrix] using this
  apply hinj
  rw [g72gk1_o_tWI_sub, ← Matrix.submatrix_mul_equiv _ _ _ e.symm _, ← Matrix.submatrix_mul_equiv _ _ _ e.symm _,
    ← Matrix.conjTranspose_submatrix, g72gk1_o_tWI_sub, g72gk1_o_pk_sub, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, g72gk1_o_pk_unit]

/-! ### g68o: polarization, tensor powers span the Bose space -/

lemma g72gk1_o_incl_excl {n : ℕ} (f : Fin n → Fin n) :
    (∑ S : Finset (Fin n), (∏ _i ∈ Finset.univ \ S, (-1 : ℂ)) *
      (if ∀ k, f k ∈ S then 1 else 0)) = if Function.Surjective f then 1 else 0 := by
  have h1 : ∀ S : Finset (Fin n), (∏ _i ∈ Finset.univ \ S, (-1 : ℂ)) * (if ∀ k, f k ∈ S then 1 else 0) =
      (∏ _i ∈ S, (1 : ℂ)) * ∏ i ∈ Finset.univ \ S, (-(if i ∈ Set.range f then (0 : ℂ) else 1)) := by
    intro S
    rw [Finset.prod_const_one, one_mul]
    by_cases hS : ∀ k, f k ∈ S
    · rw [if_pos hS, mul_one]
      refine Finset.prod_congr rfl (fun i hi => ?_)
      have : i ∉ Set.range f := by
        rintro ⟨k, rfl⟩; exact (Finset.mem_sdiff.mp hi).2 (hS k)
      rw [if_neg this]
    · rw [if_neg hS, mul_zero]
      push_neg at hS
      obtain ⟨k, hk⟩ := hS
      symm
      apply Finset.prod_eq_zero (i := f k) (by simp [hk])
      rw [if_pos ⟨k, rfl⟩, neg_zero]
  simp only [h1]
  rw [← Finset.powerset_univ, ← Finset.prod_add]
  by_cases hf : Function.Surjective f
  · rw [if_pos hf]
    apply Finset.prod_eq_one
    intro i _
    have : i ∈ Set.range f := hf i
    simp [this]
  · rw [if_neg hf]
    have : ∃ i, i ∉ Set.range f := by
      by_contra H; push_neg at H; exact hf H
    obtain ⟨i, hi⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [if_neg hi]; ring

lemma g72gk1_o_surj_sum {n : ℕ} (B : (Fin n → Fin n) → ℂ) :
    (∑ f : Fin n → Fin n, B f * (if Function.Surjective f then 1 else 0)) =
      ∑ σ : Equiv.Perm (Fin n), B σ := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun σ _ => (σ : Fin n → Fin n)) (fun σ _ => by simpa using σ.surjective)
    (fun σ _ τ _ h => Equiv.ext (congrFun h)) (fun f hf => ?_) (fun _ _ => rfl)
  have hs : Function.Surjective f := by simpa using hf
  exact ⟨Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hs, hs⟩, Finset.mem_univ _, rfl⟩

lemma g72gk1_o_polar {d n : ℕ} (x y : Word n d) :
    (∑ S : Finset (Fin n), (∏ _i ∈ Finset.univ \ S, (-1 : ℂ)) *
      ∏ k, ∑ i ∈ S, (if x i = y k then (1 : ℂ) else 0)) =
      ∑ σ : Equiv.Perm (Fin n), if y = x ∘ σ then 1 else 0 := by
  have h1 : ∀ S : Finset (Fin n), (∏ k, ∑ i ∈ S, (if x i = y k then (1 : ℂ) else 0)) =
      ∑ f : Fin n → Fin n, (if ∀ k, f k ∈ S then 1 else 0) * ∏ k, (if x (f k) = y k then (1 : ℂ) else 0) := by
    intro S
    have e : ∀ k, (∑ i ∈ S, (if x i = y k then (1 : ℂ) else 0)) =
        ∑ i, (if i ∈ S then 1 else 0) * (if x i = y k then (1 : ℂ) else 0) := by
      intro k
      rw [← Finset.sum_subset (Finset.subset_univ S)]
      · refine Finset.sum_congr rfl (fun i hi => by rw [if_pos hi, one_mul])
      · intro i _ hi; rw [if_neg hi, zero_mul]
    simp only [e]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [Finset.prod_mul_distrib]
    congr 1
    by_cases hS : ∀ k, f k ∈ S
    · rw [if_pos hS]; exact Finset.prod_eq_one (fun k _ => if_pos (hS k))
    · rw [if_neg hS]; push_neg at hS; obtain ⟨k, hk⟩ := hS
      exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ f : Fin n → Fin n, (∑ S : Finset (Fin n), (∏ _i ∈ Finset.univ \ S, (-1 : ℂ)) *
      ((if ∀ k, f k ∈ S then 1 else 0) * ∏ k, (if x (f k) = y k then (1 : ℂ) else 0))) =
      (∏ k, (if x (f k) = y k then (1 : ℂ) else 0)) * (if Function.Surjective f then 1 else 0) := by
    intro f
    rw [← g72gk1_o_incl_excl f, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _ => by ring)
  simp only [h2]
  rw [g72gk1_o_surj_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  by_cases hy : y = x ∘ σ
  · rw [if_pos hy]; exact Finset.prod_eq_one (fun k _ => if_pos (by rw [hy]; rfl))
  · rw [if_neg hy]
    have : ∃ k, x (σ k) ≠ y k := by
      by_contra H; push_neg at H; exact hy (funext fun k => (H k).symm)
    obtain ⟨k, hk⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

def g72gk1_o_phiS {d n : ℕ} (x : Word n d) (S : Finset (Fin n)) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun c => ∑ i ∈ S, if x i = c then (1 : ℂ) else 0)

lemma g72gk1_o_coh_mem {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) : coherentTensor n phi ∈ boseSpace d n := by
  intro p x
  show (∏ k, phi ((x ∘ p) k)) = ∏ k, phi (x k)
  exact Equiv.prod_comp p (fun k => phi (x k))

lemma g72gk1_o_span (d n : ℕ) :
    Submodule.span ℂ (Set.range (coherentTensor (d := d) n)) = boseSpace d n := by
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ ⟨phi, rfl⟩; exact g72gk1_o_coh_mem phi
  · intro v hv
    have hfac : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    have key : v = ∑ x : Word n d, (v x / (Nat.factorial n : ℂ)) •
        ∑ S : Finset (Fin n), (∏ _i ∈ Finset.univ \ S, (-1 : ℂ)) • coherentTensor n (g72gk1_o_phiS x S) := by
      ext y
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have e1 : ∀ x : Word n d, (∑ S : Finset (Fin n), (∏ _i ∈ Finset.univ \ S, (-1 : ℂ)) *
          (coherentTensor n (g72gk1_o_phiS x S)).ofLp y) =
          ∑ σ : Equiv.Perm (Fin n), if y = x ∘ σ then 1 else 0 := by
        intro x; rw [← g72gk1_o_polar x y]; rfl
      simp only [e1, Finset.mul_sum, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_comm]
      have e2 : ∀ σ : Equiv.Perm (Fin n), (∑ x : Word n d, if y = x ∘ σ then v x / (Nat.factorial n : ℂ) else 0) =
          v y / (Nat.factorial n : ℂ) := by
        intro σ
        rw [Finset.sum_eq_single (y ∘ σ.symm)]
        · rw [if_pos (by ext; simp)]
          have := hv σ.symm y
          rw [← this]
        · intro b _ hb; rw [if_neg]; intro h; apply hb; rw [h]; ext; simp
        · simp
      simp only [e2, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [key]
    refine Submodule.sum_mem _ (fun x _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun S _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))))

lemma g72gk1_o_tP_mulVec {d n : ℕ} (σ : Equiv.Perm (Fin n)) (w : Word n d → ℂ) (x : Word n d) :
    (Schur.tensorPermutation d n σ *ᵥ w) x = w (x ∘ σ) := by
  simp only [Matrix.mulVec, dotProduct, Schur.tensorPermutation, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (x ∘ σ)]
  · rw [if_pos (by ext k; simp)]
  · intro b _ hb; rw [if_neg]; intro h; apply hb; rw [h]; ext k; simp
  · simp

lemma g72gk1_o_act_mem {d n : ℕ} (v : TensorSpace d n) :
    QAlgorithms.act (boseProjector d n) v ∈ boseSpace d n := by
  intro p x
  show (boseProjector d n *ᵥ v.ofLp) (x ∘ p) = (boseProjector d n *ᵥ v.ofLp) x
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [g72gk1_o_linv (g72gk1_m_PP (d := d) (n := n)) p x y]

lemma g72gk1_o_act_fix {d n : ℕ} (v : TensorSpace d n) (hv : v ∈ boseSpace d n) :
    QAlgorithms.act (boseProjector d n) v = v := by
  ext x
  show (boseProjector d n *ᵥ v.ofLp) x = v x
  unfold boseProjector
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp only [Pi.smul_apply, Finset.sum_apply, g72gk1_o_tP_mulVec, smul_eq_mul]
  have : ∀ σ : Equiv.Perm (Fin n), v.ofLp (x ∘ σ) = v x := fun σ => hv σ x
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfac : ((Fintype.card (Equiv.Perm (Fin n)) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin n))).ne'
  field_simp

/-! ### g68o: coherent projectors span the Bose corner -/

def g72gk1_o_outer {ι : Type*} (u v : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.of fun x y => u x * conj (v y)

lemma g72gk1_o_geom (m e : ℕ) (hm : 0 < m) (he : e < m) :
    (∑ s ∈ Finset.range m, (Complex.exp (2 * Real.pi * Complex.I / m) ^ e) ^ s) =
      if e = 0 then (m : ℂ) else 0 := by
  have hω := Complex.isPrimitiveRoot_exp m hm.ne'
  by_cases h0 : e = 0
  · subst h0; simp
  · rw [if_neg h0]
    have hne : Complex.exp (2 * Real.pi * Complex.I / m) ^ e ≠ 1 := by
      rw [Ne, hω.pow_eq_one_iff_dvd]
      intro hd; exact h0 (Nat.eq_zero_of_dvd_of_lt hd he)
    rw [geom_sum_eq hne, ← pow_mul, show e * m = m * e from Nat.mul_comm e m, pow_mul, hω.pow_eq_one,
      one_pow, sub_self, zero_div]

lemma g72gk1_o_unit (m s : ℕ) (hm : 0 < m) :
    Complex.exp (2 * Real.pi * Complex.I / m) ^ s * conj (Complex.exp (2 * Real.pi * Complex.I / m) ^ s) = 1 := by
  have hω := Complex.isPrimitiveRoot_exp m hm.ne'
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hω.norm'_eq_one hm.ne']
  simp

lemma g72gk1_o_expand {n : ℕ} (c e : Fin n → ℂ) (z : ℂ) :
    (∏ k, (c k + z * e k)) = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((∏ k ∈ T, c k) * ∏ k ∈ Finset.univ \ T, e k) * z ^ (Finset.univ \ T).card := by
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const]; ring

lemma g72gk1_o_filter (n : ℕ) (α γ : Finset (Fin n) → ℂ) :
    (∑ s ∈ Finset.range (2 * n + 1),
      (Complex.exp (2 * Real.pi * Complex.I / (2 * n + 1 : ℕ)) ^ s) ^ n *
      (∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        α T * (Complex.exp (2 * Real.pi * Complex.I / (2 * n + 1 : ℕ)) ^ s) ^ (Finset.univ \ T).card) *
      (∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        γ T * (conj (Complex.exp (2 * Real.pi * Complex.I / (2 * n + 1 : ℕ)) ^ s)) ^ (Finset.univ \ T).card)) =
      ((2 * n + 1 : ℕ) : ℂ) * α Finset.univ * γ ∅ := by
  set m := 2 * n + 1 with hmdef
  set ω := Complex.exp (2 * Real.pi * Complex.I / (m : ℕ))
  have hm : 0 < m := by omega
  have hk : ∀ T : Finset (Fin n), (Finset.univ \ T).card ≤ n := fun T =>
    (Finset.card_le_univ _).trans (by simp)
  have hz : ∀ s (T T' : Finset (Fin n)), (ω ^ s) ^ n * (ω ^ s) ^ (Finset.univ \ T).card *
      (conj (ω ^ s)) ^ (Finset.univ \ T').card =
      (ω ^ ((Finset.univ \ T).card + n - (Finset.univ \ T').card)) ^ s := by
    intro s T T'
    have h1 : (ω ^ s) ^ n = (ω ^ s) ^ (n - (Finset.univ \ T').card) * (ω ^ s) ^ (Finset.univ \ T').card := by
      rw [← pow_add, Nat.sub_add_cancel (hk T')]
    rw [h1]
    have h2 : (ω ^ s) ^ (Finset.univ \ T').card * (conj (ω ^ s)) ^ (Finset.univ \ T').card = 1 := by
      rw [← mul_pow, g72gk1_o_unit m s hm, one_pow]
    calc _ = (ω ^ s) ^ (n - (Finset.univ \ T').card) * (ω ^ s) ^ (Finset.univ \ T).card *
          ((ω ^ s) ^ (Finset.univ \ T').card * (conj (ω ^ s)) ^ (Finset.univ \ T').card) := by ring
      _ = _ := by
        rw [h2, mul_one, ← pow_add, ← pow_mul, ← pow_mul, mul_comm]
        congr 2; have := hk T'; omega
  have hexp : ∀ s, (ω ^ s) ^ n *
      (∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, α T * (ω ^ s) ^ (Finset.univ \ T).card) *
      (∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, γ T * (conj (ω ^ s)) ^ (Finset.univ \ T).card) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, ∑ T' ∈ (Finset.univ : Finset (Fin n)).powerset,
        α T * γ T' * (ω ^ ((Finset.univ \ T).card + n - (Finset.univ \ T').card)) ^ s := by
    intro s
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun T _ => Finset.sum_congr rfl (fun T' _ => ?_))
    rw [← hz s T T']; ring
  simp only [hexp]
  rw [Finset.sum_comm]
  have hin : ∀ T ∈ (Finset.univ : Finset (Fin n)).powerset,
      (∑ s ∈ Finset.range m, ∑ T' ∈ (Finset.univ : Finset (Fin n)).powerset,
        α T * γ T' * (ω ^ ((Finset.univ \ T).card + n - (Finset.univ \ T').card)) ^ s) =
      ∑ T' ∈ (Finset.univ : Finset (Fin n)).powerset,
        if T = Finset.univ ∧ T' = ∅ then (m : ℂ) * α T * γ T' else 0 := by
    intro T _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun T' _ => ?_)
    rw [← Finset.mul_sum, g72gk1_o_geom m _ hm (by have := hk T; have := hk T'; omega)]
    have hiff : (Finset.univ \ T).card + n - (Finset.univ \ T').card = 0 ↔ T = Finset.univ ∧ T' = ∅ := by
      have c1 : (Finset.univ \ T).card = 0 ↔ T = Finset.univ := by
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.univ_subset_iff]
      have c2 : (Finset.univ \ T').card = n ↔ T' = ∅ := by
        rw [Finset.card_univ_diff, Fintype.card_fin]
        constructor
        · intro h; have : T'.card ≤ n := (Finset.card_le_univ _).trans (by simp)
          exact Finset.card_eq_zero.mp (by omega)
        · intro h; subst h; simp
      have := hk T'
      constructor
      · intro h; exact ⟨c1.mp (by omega), c2.mp (by omega)⟩
      · rintro ⟨h1, h2⟩; have := c1.mpr h1; have := c2.mpr h2; omega
    by_cases hc : T = Finset.univ ∧ T' = ∅
    · rw [if_pos (hiff.mpr hc), if_pos hc]; ring
    · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc, mul_zero]
  rw [Finset.sum_congr rfl hin]
  rw [Finset.sum_eq_single Finset.univ]
  · rw [Finset.sum_eq_single ∅]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro b _ hb; rw [if_neg (fun h => hb h.2)]
    · intro h; exact absurd (Finset.empty_mem_powerset _) h
  · intro b _ hb
    exact Finset.sum_eq_zero (fun T' _ => if_neg (fun h => hb h.1))
  · intro h; exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h

lemma g72gk1_o_outer_coh {d n : ℕ} (a b : EuclideanSpace ℂ (Fin d)) :
    g72gk1_o_outer (coherentTensor n a) (coherentTensor n b) =
      (((2 * n + 1 : ℕ) : ℂ))⁻¹ • ∑ s ∈ Finset.range (2 * n + 1),
        (Complex.exp (2 * Real.pi * Complex.I / (2 * n + 1 : ℕ)) ^ s) ^ n •
          pureDensity (coherentTensor n (a + (Complex.exp (2 * Real.pi * Complex.I / (2 * n + 1 : ℕ)) ^ s) • b)) := by
  set ω := Complex.exp (2 * Real.pi * Complex.I / (2 * n + 1 : ℕ))
  ext x y
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, pureDensity, g72gk1_o_outer, Matrix.of_apply, g72gk1_j_pvc,
    PiLp.add_apply, PiLp.smul_apply]
  have hket : ∀ s, (∏ k, (a (x k) + ω ^ s * b (x k))) = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((∏ k ∈ T, a (x k)) * ∏ k ∈ Finset.univ \ T, b (x k)) * (ω ^ s) ^ (Finset.univ \ T).card :=
    fun s => g72gk1_o_expand (fun k => a (x k)) (fun k => b (x k)) (ω ^ s)
  have hbra : ∀ s, conj (∏ k, (a (y k) + ω ^ s * b (y k))) = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((∏ k ∈ T, conj (a (y k))) * ∏ k ∈ Finset.univ \ T, conj (b (y k))) * (conj (ω ^ s)) ^ (Finset.univ \ T).card := by
    intro s
    rw [map_prod]
    simp only [map_add, map_mul]
    exact g72gk1_o_expand (fun k => conj (a (y k))) (fun k => conj (b (y k))) (conj (ω ^ s))
  simp only [smul_eq_mul, hket, hbra]
  have hf := g72gk1_o_filter n (fun T => (∏ k ∈ T, a (x k)) * ∏ k ∈ Finset.univ \ T, b (x k))
    (fun T => (∏ k ∈ T, conj (a (y k))) * ∏ k ∈ Finset.univ \ T, conj (b (y k)))
  have hf' : (∑ s ∈ Finset.range (2 * n + 1), (ω ^ s) ^ n *
      ((∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((∏ k ∈ T, a (x k)) * ∏ k ∈ Finset.univ \ T, b (x k)) * (ω ^ s) ^ (Finset.univ \ T).card) *
      (∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((∏ k ∈ T, conj (a (y k))) * ∏ k ∈ Finset.univ \ T, conj (b (y k))) * (conj (ω ^ s)) ^ (Finset.univ \ T).card))) =
      ((2 * n + 1 : ℕ) : ℂ) * ((∏ k ∈ Finset.univ, a (x k)) * ∏ k ∈ Finset.univ \ Finset.univ, b (x k)) *
        ((∏ k ∈ (∅ : Finset (Fin n)), conj (a (y k))) * ∏ k ∈ Finset.univ \ ∅, conj (b (y k))) := by
    rw [← hf]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  rw [hf']
  simp only [Finset.sdiff_self, Finset.prod_empty, mul_one, one_mul, Finset.sdiff_empty, map_prod]
  have : ((2 * n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
  field_simp

lemma g72gk1_o_pd_mem {d n : ℕ} (hn : 1 ≤ n) (χ : EuclideanSpace ℂ (Fin d)) :
    pureDensity (coherentTensor n χ) ∈ Submodule.span ℂ {B : TensorMat d n |
        ∃ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 ∧ B = pureDensity (coherentTensor n phi)} := by
  by_cases h0 : χ = 0
  · have : pureDensity (coherentTensor n χ) = 0 := by
      ext x y
      simp only [pureDensity, Matrix.of_apply, g72gk1_j_pvc, h0, Matrix.zero_apply]
      rw [Finset.prod_eq_zero (Finset.mem_univ ⟨0, by omega⟩) (by simp)]; simp
    rw [this]; exact Submodule.zero_mem _
  · have hr : ‖χ‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    set ψ : EuclideanSpace ℂ (Fin d) := ((‖χ‖⁻¹ : ℝ) : ℂ) • χ with hψdef
    have hψ : ‖ψ‖ = 1 := by
      rw [hψdef, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hr]
    have hgen : ∀ c : ℝ, pureDensity (coherentTensor n ((c : ℂ) • χ)) =
        ((c ^ (2 * n) : ℝ) : ℂ) • pureDensity (coherentTensor n χ) := by
      intro c; ext x y
      simp only [pureDensity, Matrix.of_apply, Matrix.smul_apply, g72gk1_j_pvc, smul_eq_mul,
        PiLp.smul_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        map_mul, map_pow, Complex.conj_ofReal]
      push_cast; ring
    have : pureDensity (coherentTensor n χ) = (((‖χ‖ ^ (2 * n) : ℝ)) : ℂ) • pureDensity (coherentTensor n ψ) := by
      rw [hψdef, hgen, smul_smul, ← Complex.ofReal_mul, ← mul_pow, mul_inv_cancel₀ hr, one_pow,
        Complex.ofReal_one, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ψ, hψ, rfl⟩)

lemma g72gk1_o_outer_add_l {ι : Type*} (u u' v : EuclideanSpace ℂ ι) :
    g72gk1_o_outer (u + u') v = g72gk1_o_outer u v + g72gk1_o_outer u' v := by
  ext x y; simp [g72gk1_o_outer]; ring
lemma g72gk1_o_outer_add_r {ι : Type*} (u v v' : EuclideanSpace ℂ ι) :
    g72gk1_o_outer u (v + v') = g72gk1_o_outer u v + g72gk1_o_outer u v' := by
  ext x y; simp [g72gk1_o_outer]; ring
lemma g72gk1_o_outer_smul_l {ι : Type*} (c : ℂ) (u v : EuclideanSpace ℂ ι) :
    g72gk1_o_outer (c • u) v = c • g72gk1_o_outer u v := by
  ext x y; simp [g72gk1_o_outer]; ring
lemma g72gk1_o_outer_smul_r {ι : Type*} (c : ℂ) (u v : EuclideanSpace ℂ ι) :
    g72gk1_o_outer u (c • v) = (conj c) • g72gk1_o_outer u v := by
  ext x y; simp [g72gk1_o_outer]; ring
lemma g72gk1_o_outer_zero_l {ι : Type*} (v : EuclideanSpace ℂ ι) : g72gk1_o_outer 0 v = 0 := by
  ext x y; simp [g72gk1_o_outer]
lemma g72gk1_o_outer_zero_r {ι : Type*} (u : EuclideanSpace ℂ ι) : g72gk1_o_outer u 0 = 0 := by
  ext x y; simp [g72gk1_o_outer]

lemma g72gk1_o_outer_span {d n : ℕ} (hn : 1 ≤ n) (u v : TensorSpace d n)
    (hu : u ∈ Submodule.span ℂ (Set.range (coherentTensor (d := d) n)))
    (hv : v ∈ Submodule.span ℂ (Set.range (coherentTensor (d := d) n))) :
    g72gk1_o_outer u v ∈ Submodule.span ℂ {B : TensorMat d n |
        ∃ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 ∧ B = pureDensity (coherentTensor n phi)} := by
  have step1 : ∀ a : EuclideanSpace ℂ (Fin d), ∀ v ∈ Submodule.span ℂ (Set.range (coherentTensor (d := d) n)),
      g72gk1_o_outer (coherentTensor n a) v ∈ Submodule.span ℂ {B : TensorMat d n |
        ∃ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 ∧ B = pureDensity (coherentTensor n phi)} := by
    intro a v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [g72gk1_o_outer_coh]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun s _ => Submodule.smul_mem _ _ (g72gk1_o_pd_mem hn _)))
    | zero => rw [g72gk1_o_outer_zero_r]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [g72gk1_o_outer_add_r]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [g72gk1_o_outer_smul_r]; exact Submodule.smul_mem _ _ hx
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact step1 a v hv
  | zero => rw [g72gk1_o_outer_zero_l]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [g72gk1_o_outer_add_l]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [g72gk1_o_outer_smul_l]; exact Submodule.smul_mem _ _ hx

def g72gk1_o_col {d n : ℕ} (x : Word n d) : TensorSpace d n :=
  WithLp.toLp 2 (fun i : Word n d => (boseProjector d n : Matrix (Word n d) (Word n d) ℂ) i x)

lemma g72gk1_o_col_mem {d n : ℕ} (x : Word n d) :
    g72gk1_o_col x ∈ Submodule.span ℂ (Set.range (coherentTensor (d := d) n)) := by
  rw [g72gk1_o_span]
  intro p i
  exact g72gk1_o_linv (g72gk1_m_PP (d := d) (n := n)) p i x

lemma g72gk1_o_cps {d n : ℕ} (hn : 1 ≤ n) (A : TensorMat d n) :
    (A ∈ Submodule.span ℂ {B : TensorMat d n |
        ∃ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 ∧
          B = QAlgorithms.pureDensity (coherentTensor n phi)}) ↔ BoseSupported A := by
  constructor
  · intro hA
    induction hA using Submodule.span_induction with
    | mem x hx => obtain ⟨phi, _, rfl⟩ := hx; exact ⟨g72gk1_j_PD phi, g72gk1_j_DP phi⟩
    | zero => exact ⟨by simp, by simp⟩
    | add x y _ _ hx hy => exact ⟨by rw [Matrix.mul_add, hx.1, hy.1], by rw [Matrix.add_mul, hx.2, hy.2]⟩
    | smul c x _ hx => exact ⟨by rw [Matrix.mul_smul, hx.1], by rw [Matrix.smul_mul, hx.2]⟩
  · intro hA
    have hPAP : A = boseProjector d n * A * boseProjector d n := by rw [hA.1, hA.2]
    have key : A = ∑ x : Word n d, ∑ y : Word n d, A x y • g72gk1_o_outer (g72gk1_o_col x) (g72gk1_o_col y) := by
      conv_lhs => rw [hPAP]
      ext i j
      simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, g72gk1_o_outer, g72gk1_o_col,
        Matrix.of_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      have hH : boseProjector d n y j = conj (boseProjector d n j y) := by
        conv_lhs => rw [← g72gk1_o_P_H (d := d) (n := n)]
        rfl
      rw [hH]; ring
    rw [key]
    exact Submodule.sum_mem _ (fun x _ => Submodule.sum_mem _ (fun y _ =>
      Submodule.smul_mem _ _ (g72gk1_o_outer_span hn _ _ (g72gk1_o_col_mem x) (g72gk1_o_col_mem y))))

/-! ### g72gk1: Bose irreducibility -/

lemma g72gk1_col {d : ℕ} (hd : 0 < d) (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    ∃ u : Matrix.unitaryGroup (Fin d) ℂ,
      act (u : Matrix (Fin d) (Fin d) ℂ) (EuclideanSpace.single ⟨0, hd⟩ 1) = phi := by
  have hv : Orthonormal ℂ (({⟨0, hd⟩} : Set (Fin d)).domRestrict (fun _ : Fin d => phi)) := by
    constructor
    · intro i; simpa using hphi
    · intro i j hij
      exfalso; apply hij
      obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j
      simp only [Set.mem_singleton_iff] at hi hj
      subst hi; subst hj; rfl
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨⟨(EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b,
    (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩, ?_⟩
  have hb0 : b ⟨0, hd⟩ = phi := by simpa using hb ⟨0, hd⟩ rfl
  ext i
  simp [act, Module.Basis.toMatrix_apply, hb0]

lemma g72gk1_inv {d n : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (v : TensorSpace d n)
    (hv : v ∈ boseSpace d n) : act (piKron n U) v ∈ boseSpace d n := by
  intro p x
  simp only [act, Matrix.mulVec, dotProduct, piKron, Matrix.of_apply, Function.comp_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr p (Equiv.refl _)) _ _ (fun y => ?_)
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.id_comp]
  congr 1
  · rw [← Equiv.prod_comp p (fun k => U (x k) ((y ∘ p.symm) k))]
    simp
  · exact (hv p.symm y).symm

lemma g72gk1_tP_one {d n : ℕ} : Schur.tensorPermutation d n 1 = 1 := by
  ext y x
  rfl

lemma g72gk1_trP_small {d n : ℕ} (hn : n ≤ 1) : boseProjector d n = 1 := by
  unfold boseProjector
  have : ∀ p : Equiv.Perm (Fin n), p = 1 := fun p => by
    ext k; have := k.isLt; have := (p k).isLt; omega
  rw [Fintype.sum_eq_single 1 (fun p hp => absurd (this p) hp), g72gk1_tP_one]
  have hc : Fintype.card (Equiv.Perm (Fin n)) = 1 := by
    rw [Fintype.card_perm, Fintype.card_fin]; interval_cases n <;> rfl
  rw [hc]; simp

lemma g72gk1_trP {d : ℕ} (hd : 0 < d) : ∀ n, (boseProjector d n).trace = boseDimension d n := by
  intro n
  induction n with
  | zero =>
    rw [g72gk1_trP_small (by omega), Matrix.trace_one]
    simp [boseDimension]
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · subst h0
      rw [g72gk1_trP_small (by omega), Matrix.trace_one]
      simp [boseDimension]
    · have hPP := g72gk1_m_PP (d := d) (n := N)
      have key := g72gk1_o_Rlast hN (boseProjector d N) hPP hPP
      have habs : boseProjector d (N+1) * tensorWithIdentity (Nat.le_succ N) (boseProjector d N) *
          boseProjector d (N+1) = boseProjector d (N+1) := by
        rw [g72gk1_m_absorb_l, g72gk1_m_PP]
      rw [habs] at key
      have htr := g72gk1_o_trace_R (Fin.last N) (boseProjector d (N+1))
      have htr0 := g72gk1_o_trace_R (⟨0, by omega⟩ : Fin N) (boseProjector d N)
      rw [Matrix.trace] at htr htr0
      simp only [Matrix.diag, key] at htr
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at htr
      simp only [if_true] at htr
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htr
      rw [show (∑ i, g72gk1_o_R (⟨0, by omega⟩ : Fin N) (boseProjector d N) i i) =
        (boseProjector d N).trace from htr0, ih] at htr
      have hb := g72gk1_o_bD_succ d N hd
      have hN1 : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (show N + 1 ≠ 0 by omega)
      rw [← htr]
      apply mul_right_cancel₀ hN1
      rw [hb]
      field_simp
      ring

lemma g72gk1_pk_coh {d n : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (phi : EuclideanSpace ℂ (Fin d)) :
    piKron n U * pureDensity (coherentTensor n phi) * (piKron n U)ᴴ =
      pureDensity (coherentTensor n (act U phi)) := by
  have hv : ∀ x, ∑ a, piKron n U x a * coherentTensor n phi a = coherentTensor n (act U phi) x := by
    intro x
    simp only [piKron, Matrix.of_apply, coherentTensor, powerVector, act, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun i c => U (x i) c * phi c)]
    simp [Matrix.mulVec, dotProduct]
  ext x y
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply, Matrix.conjTranspose_apply]
  rw [← hv x, ← hv y, map_sum, Finset.sum_mul_sum, Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul, Complex.star_def]
  ring

lemma g72gk1_pk_unit' {d n : ℕ} (u : Matrix.unitaryGroup (Fin d) ℂ) :
    (piKron n (u : Matrix (Fin d) (Fin d) ℂ))ᴴ * piKron n (u : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  rw [g72gk1_o_pk_H, g72gk1_o_pk_mul]
  have : (u : Matrix (Fin d) (Fin d) ℂ)ᴴ * (u : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp u.2
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [this, g72gk1_o_pk_one]

lemma g72gk1_comm {d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) (A : TensorMat d n) (hA : BoseSupported A)
    (hc : ∀ u : Matrix.unitaryGroup (Fin d) ℂ, A * piKron n (u : Matrix (Fin d) (Fin d) ℂ) =
      piKron n (u : Matrix (Fin d) (Fin d) ℂ) * A) :
    ∃ c : ℂ, A = c • boseProjector d n := by
  set e0 : EuclideanSpace ℂ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ 1 with he0
  have he0n : ‖e0‖ = 1 := by simp [he0]
  set c := (A * pureDensity (coherentTensor n e0)).trace with hcdef
  refine ⟨c, ?_⟩
  set B := A - c • boseProjector d n with hBdef
  have hBc : ∀ u : Matrix.unitaryGroup (Fin d) ℂ,
      (piKron n (u : Matrix (Fin d) (Fin d) ℂ))ᴴ * B * piKron n (u : Matrix (Fin d) (Fin d) ℂ) = B := by
    intro u
    have h1 : B * piKron n (u : Matrix (Fin d) (Fin d) ℂ) = piKron n (u : Matrix (Fin d) (Fin d) ℂ) * B := by
      rw [hBdef, Matrix.sub_mul, Matrix.mul_sub, hc u, Matrix.smul_mul, Matrix.mul_smul, g72gk1_o_pk_P]
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, g72gk1_pk_unit', Matrix.one_mul]
  have hf : ∀ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 →
      (B * pureDensity (coherentTensor n phi)).trace = 0 := by
    intro phi hphi
    obtain ⟨u, hu⟩ := g72gk1_col hd phi hphi
    rw [← hu, ← g72gk1_pk_coh]
    set Q := piKron n (u : Matrix (Fin d) (Fin d) ℂ)
    set W := pureDensity (coherentTensor n e0)
    rw [show B * (Q * W * Qᴴ) = (B * Q * W) * Qᴴ by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm,
      show Qᴴ * (B * Q * W) = (Qᴴ * B * Q) * W by simp only [Matrix.mul_assoc], hBc u]
    rw [hBdef, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, g72gk1_j_PD,
      g72gk1_o_coh_trace e0 he0n, ← hcdef]
    simp
  have hspan : ∀ X ∈ Submodule.span ℂ {Y : TensorMat d n |
        ∃ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 ∧ Y = QAlgorithms.pureDensity (coherentTensor n phi)},
      (B * X).trace = 0 := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem Y hY => obtain ⟨phi, hphi, rfl⟩ := hY; exact hf phi hphi
    | zero => simp
    | add Y Z _ _ hY hZ => rw [Matrix.mul_add, Matrix.trace_add, hY, hZ, add_zero]
    | smul a Y _ hY => rw [Matrix.mul_smul, Matrix.trace_smul, hY, smul_zero]
  have hBs : BoseSupported Bᴴ := by
    have hPH := g72gk1_o_P_H (d := d) (n := n)
    have hPP := g72gk1_m_PP (d := d) (n := n)
    have hl : boseProjector d n * B = B := by
      rw [hBdef, Matrix.mul_sub, Matrix.mul_smul, hA.1, hPP]
    have hr : B * boseProjector d n = B := by
      rw [hBdef, Matrix.sub_mul, Matrix.smul_mul, hA.2, hPP]
    constructor
    · rw [← hPH, ← Matrix.conjTranspose_mul, hr]
    · rw [← hPH, ← Matrix.conjTranspose_mul, hl]
  have h0 := hspan Bᴴ ((g72gk1_o_cps hn Bᴴ).mpr hBs)
  have hB0 : Bᴴ = 0 := by
    rw [← Matrix.trace_conjTranspose_mul_self_eq_zero_iff, Matrix.conjTranspose_conjTranspose]
    exact h0
  have : B = 0 := by simpa using congrArg Matrix.conjTranspose hB0
  rw [hBdef] at this
  exact sub_eq_zero.mp this


lemma g72gk1_tPA {d n : ℕ} (σ : Equiv.Perm (Fin n)) (A : TensorMat d n) (x y : Word n d) :
    (Schur.tensorPermutation d n σ * A) x y = A (x ∘ σ) y := by
  simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (x ∘ σ)]
  · rw [if_pos (by ext k; simp)]
  · intro b _ hb; rw [if_neg]; intro h; apply hb; rw [h]; ext k; simp
  · simp


lemma g72gk1_quad {I : Type*} [Fintype I] (A : Matrix I I ℂ) (v : I → ℂ) :
    star v ⬝ᵥ (A *ᵥ v) = ∑ x, ∑ y, (star (v x) * v y) * A x y := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring


/-! channel output positivity and overlap bounds -/

lemma g72gk1_out_psd {d N M : ℕ} (T : CloneMap d N M) (hT : IsBoseInputChannel T)
    (A : TensorMat d N) (hA : A.PosSemidef) : (T A).PosSemidef := by
  obtain ⟨⟨L, hTL, hCP⟩, -, -⟩ := hT
  have h := hCP 1 (A.submatrix Prod.snd Prod.snd) (hA.submatrix _)
  have : T A = (idTensorSuperop L (A.submatrix Prod.snd Prod.snd)).submatrix
      (fun j => ((0 : Fin 1), j)) (fun j => ((0 : Fin 1), j)) := by
    ext x y
    simp only [Matrix.submatrix_apply, idTensorSuperop, Matrix.of_apply, hTL]
    rfl
  rw [this]; exact h.submatrix _

lemma g72gk1_pure_psd {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    (pureDensity v).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext x y; simp [pureDensity, Matrix.conjTranspose_apply, mul_comm]
  · intro w
    rw [g72gk1_quad]
    have : ∑ x, ∑ y, (star (w x) * w y) * pureDensity v x y =
        ((‖∑ x, star (w x) * v x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [pureDensity, Matrix.of_apply, map_mul, Complex.star_def, Complex.conj_conj]
      ring
    rw [this]; exact Complex.zero_le_real.mpr (by positivity)

lemma g72gk1_pure_H {ι : Type*} (v : EuclideanSpace ℂ ι) : (pureDensity v)ᴴ = pureDensity v := by
  ext x y; simp [pureDensity, Matrix.conjTranspose_apply, mul_comm]

lemma g72gk1_pure_idem {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι)
    (hv : ∑ a, v a * conj (v a) = 1) : pureDensity v * pureDensity v = pureDensity v := by
  ext a c
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply]
  calc _ = v a * conj (v c) * ∑ b, v b * conj (v b) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)
    _ = _ := by rw [hv, mul_one]

lemma g72gk1_tr_nonneg {I : Type*} [Fintype I] (E ρ : Matrix I I ℂ) (hE : Eᴴ = E) (hEE : E * E = E)
    (hρ : ρ.PosSemidef) : 0 ≤ (E * ρ).trace.re := by
  have h1 : (E * ρ).trace = (E * ρ * Eᴴ).trace := by
    rw [hE, Matrix.trace_mul_comm (E * ρ) E, ← Matrix.mul_assoc, hEE]
  rw [h1]; exact (Complex.nonneg_iff.mp (hρ.mul_mul_conjTranspose_same E).trace_nonneg).1

lemma g72gk1_coh_norm {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    ∑ u : Word n d, coherentTensor n phi u * conj (coherentTensor n phi u) = 1 := by
  simp only [coherentTensor, powerVector, map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin n) a => phi a * conj (phi a))]
  have : ∑ a, phi a * conj (phi a) = 1 := by
    have h2 : ‖phi‖ ^ 2 = 1 := by rw [hphi]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h2
    simp only [Complex.mul_conj']
    exact_mod_cast h2
  simp [this]

lemma g72gk1_tP_H {d n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Schur.tensorPermutation d n σ)ᴴ = Schur.tensorPermutation d n σ⁻¹ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, Schur.tensorPermutation, Matrix.of_apply]
  rw [apply_ite (star : ℂ → ℂ), star_one, star_zero]
  congr 1
  apply propext
  constructor
  · intro h; rw [h]; ext k; simp [Equiv.Perm.inv_def]
  · intro h; rw [h]; ext k; simp [Equiv.Perm.inv_def]

lemma g72gk1_P_H {d n : ℕ} : (boseProjector d n)ᴴ = boseProjector d n := by
  unfold boseProjector
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [g72gk1_tP_H]
  congr 1
  · simp
  · exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun _ => rfl)

lemma g72gk1_coh_PD {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
    boseProjector d n * pureDensity (coherentTensor n phi) = pureDensity (coherentTensor n phi) := by
  have hp : ∀ p : Equiv.Perm (Fin n),
      Schur.tensorPermutation d n p * pureDensity (coherentTensor n phi) =
        pureDensity (coherentTensor n phi) := by
    intro p
    ext y z
    rw [g72gk1_tPA]
    simp only [pureDensity, Matrix.of_apply, coherentTensor, powerVector, Function.comp_apply]
    congr 1
    exact Equiv.prod_comp p (fun k => phi (y k))
  rw [boseProjector, Matrix.smul_mul, Finset.sum_mul]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin n))).ne'), one_smul]

lemma g72gk1_coh_DP {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
    pureDensity (coherentTensor n phi) * boseProjector d n = pureDensity (coherentTensor n phi) := by
  have h := congrArg Matrix.conjTranspose (g72gk1_coh_PD (n := n) phi)
  rw [Matrix.conjTranspose_mul, g72gk1_pure_H] at h
  rwa [g72gk1_P_H] at h

lemma g72gk1_ov_bounds {d N M : ℕ} (T : CloneMap d N M) (hT : IsBoseInputChannel T)
    (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    0 ≤ cloningOverlap T phi ∧ cloningOverlap T phi ≤ 1 := by
  have hρ := g72gk1_out_psd T hT _ (g72gk1_pure_psd (coherentTensor N phi))
  have hE := g72gk1_pure_H (coherentTensor M phi)
  have hEE := g72gk1_pure_idem (coherentTensor M phi) (g72gk1_coh_norm phi hphi)
  refine ⟨g72gk1_tr_nonneg _ _ hE hEE hρ, ?_⟩
  have h2 := g72gk1_tr_nonneg (1 - pureDensity (coherentTensor M phi)) _
    (by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hE])
    (by rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hEE, Matrix.one_mul, Matrix.mul_one,
          Matrix.one_mul]; abel) hρ
  have htr : (T (pureDensity (coherentTensor N phi))).trace = 1 := by
    rw [hT.2.2, Matrix.mul_assoc, g72gk1_coh_DP, g72gk1_coh_PD]
    rw [← g72gk1_coh_norm (n := N) phi hphi]; rfl
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul, htr] at h2
  unfold cloningOverlap
  simp only [Complex.sub_re, Complex.one_re] at h2
  linarith


lemma g72gk1_fid_le {d N M : ℕ} (T : CloneMap d N M) (hT : IsBoseInputChannel T)
    (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) : cloningFidelity T ≤ cloningOverlap T phi :=
  csInf_le ⟨0, by rintro r ⟨ψ, hψ, rfl⟩; exact (g72gk1_ov_bounds T hT ψ hψ).1⟩ ⟨phi, hphi, rfl⟩

lemma g72gk1_unit_exists {d : ℕ} (hd : 0 < d) : ∃ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, hd⟩ 1, by simp⟩

lemma g72gk1_fid_le_one {d N M : ℕ} (hd : 0 < d) (T : CloneMap d N M) (hT : IsBoseInputChannel T) :
    cloningFidelity T ≤ 1 := by
  obtain ⟨phi, hphi⟩ := g72gk1_unit_exists hd
  exact (g72gk1_fid_le T hT phi hphi).trans (g72gk1_ov_bounds T hT phi hphi).2


lemma g72gk1b_quad {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) (i j : ι) (hij : i ≠ j) (w : ℂ) :
    star (Pi.single i 1 + Pi.single j w : ι → ℂ) ⬝ᵥ (Y *ᵥ (Pi.single i 1 + Pi.single j w)) =
      Y i i + Y i j * w + star w * Y j i + star w * Y j j * w := by
  simp only [dotProduct, Matrix.mulVec, Pi.add_apply, Pi.star_apply, Pi.single_apply, mul_add,
    Finset.sum_add_distrib, add_mul, star_add]
  simp only [apply_ite star, star_one, star_zero, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, zero_add]
  ring

lemma g72gk1b_psd_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) (hY : Y.PosSemidef)
    (i j : ι) : ‖Y i j‖ ≤ 2 * ‖Y.trace‖ := by
  have hdiag : ∀ k, 0 ≤ Y k k := fun k => hY.diag_nonneg
  have htr : Y.trace = ∑ k, Y k k := rfl
  have hre : ∀ k, (Y k k).im = 0 := fun k => ((Complex.nonneg_iff.mp (hdiag k)).2).symm
  have hre0 : ∀ k, 0 ≤ (Y k k).re := fun k => (Complex.nonneg_iff.mp (hdiag k)).1
  have htrre : ‖Y.trace‖ = ∑ k, (Y k k).re := by
    have : Y.trace = ((∑ k, (Y k k).re : ℝ) : ℂ) := by
      rw [htr]; push_cast; exact Finset.sum_congr rfl fun k _ => Complex.ext (by simp) (by simp [hre k])
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => hre0 k)]
  have hle : ∀ k, (Y k k).re ≤ ‖Y.trace‖ := fun k => by
    rw [htrre]; exact Finset.single_le_sum (fun k _ => hre0 k) (Finset.mem_univ k)
  by_cases hij : i = j
  · subst hij
    have : ‖Y i i‖ = (Y i i).re := by
      rw [show Y i i = ((Y i i).re : ℂ) from Complex.ext (by simp) (by simp [hre i]), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hre0 i)]; simp
    rw [this]; linarith [hle i, norm_nonneg Y.trace]
  · have hH : Y j i = star (Y i j) := by
      have := congrFun (congrFun hY.1 j) i
      rw [Matrix.conjTranspose_apply] at this; exact this.symm
    have hq : ∀ w : ℂ, star w * w = 1 → 0 ≤ ((Y i i).re + (Y j j).re + 2 * (Y i j * w).re) := by
      intro w hw
      have h0 := hY.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j w)
      rw [g72gk1b_quad Y i j hij w, hH] at h0
      have h1 := (Complex.nonneg_iff.mp h0).1
      have e1 : star w * Y j j * w = Y j j := by linear_combination (Y j j) * hw
      rw [e1] at h1
      simp only [Complex.add_re] at h1
      have e2 : (star w * star (Y i j)).re = (Y i j * w).re := by
        rw [← star_mul', mul_comm]; simp [Complex.star_def]
      linarith
    have h1 := hq 1 (by simp)
    have h2 := hq (-1) (by simp)
    have h3 := hq Complex.I (by simp [Complex.star_def])
    have h4 := hq (-Complex.I) (by simp [Complex.star_def])
    simp only [mul_one, mul_neg, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
      zero_sub, Complex.one_re] at h1 h2 h3 h4
    have hn : ‖Y i j‖ ≤ |(Y i j).re| + |(Y i j).im| := Complex.norm_le_abs_re_add_abs_im _
    have hre' : |(Y i j).re| ≤ ((Y i i).re + (Y j j).re) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have him' : |(Y i j).im| ≤ ((Y i i).re + (Y j j).re) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith [hle i, hle j]

abbrev g72gk1b_V (d N M : ℕ) := Word N d → Word N d → Word M d → Word M d → ℂ

def g72gk1b_rec {d N M : ℕ} (c : g72gk1b_V d N M) : CloneMap d N M :=
  fun A => Matrix.of fun i j => ∑ x, ∑ y, A x y * c x y i j

def g72gk1b_recL {d N M : ℕ} (c : g72gk1b_V d N M) : TensorMat d N →ₗ[ℂ] TensorMat d M where
  toFun := g72gk1b_rec c
  map_add' A B := by
    ext i j; simp [g72gk1b_rec, add_mul, Finset.sum_add_distrib]
  map_smul' a A := by
    ext i j; simp [g72gk1b_rec, Finset.mul_sum, mul_assoc]

def g72gk1b_coef {d N M : ℕ} (T : CloneMap d N M) : g72gk1b_V d N M :=
  fun x y i j => T (Matrix.single x y 1) i j

lemma g72gk1b_rec_coef {d N M : ℕ} (T : CloneMap d N M) (L : TensorMat d N →ₗ[ℂ] TensorMat d M)
    (hTL : ∀ A, T A = L A) : g72gk1b_rec (g72gk1b_coef T) = T := by
  funext A
  ext i j
  rw [hTL A]
  conv_rhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, Matrix.sum_apply, g72gk1b_rec, g72gk1b_coef, Matrix.of_apply, hTL]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [show Matrix.single x y (A x y) = A x y • Matrix.single x y (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, Matrix.smul_apply, smul_eq_mul]

lemma g72gk1b_rec_single {d N M : ℕ} (c : g72gk1b_V d N M) (x y : Word N d) (i j : Word M d) :
    g72gk1b_rec c (Matrix.single x y 1) i j = c x y i j := by
  simp only [g72gk1b_rec, Matrix.of_apply, Matrix.single_apply]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma g72gk1b_K_iff {d N M : ℕ} (c : g72gk1b_V d N M) :
    IsBoseInputChannel (g72gk1b_rec c) ↔
      (Entanglement.IsCompletelyPositive (g72gk1b_recL c) ∧
        (∀ A, g72gk1b_rec c A = g72gk1b_rec c (boseProjector d N * A * boseProjector d N)) ∧
        ∀ A, (g72gk1b_rec c A).trace = (boseProjector d N * A * boseProjector d N).trace) := by
  constructor
  · rintro ⟨⟨L, hTL, hCP⟩, h2, h3⟩
    have : L = g72gk1b_recL c := LinearMap.ext fun A => (hTL A).symm
    subst this
    exact ⟨hCP, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨g72gk1b_recL c, fun A => rfl, h1⟩, h2, h3⟩

lemma g72gk1b_cont {d N M : ℕ} (A : TensorMat d N) (i j : Word M d) :
    Continuous fun c : g72gk1b_V d N M => g72gk1b_rec c A i j := by
  simp only [g72gk1b_rec, Matrix.of_apply]
  fun_prop

lemma g72gk1b_contM {d N M : ℕ} (A : TensorMat d N) :
    Continuous fun c : g72gk1b_V d N M => g72gk1b_rec c A :=
  continuous_pi fun i => continuous_pi fun j => g72gk1b_cont A i j

lemma g72gk1b_psd_closed {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsClosed {Y : Matrix ι ι ℂ | Y.PosSemidef} := by
  have : {Y : Matrix ι ι ℂ | Y.PosSemidef} =
      {Y | Yᴴ = Y} ∩ ⋂ v : ι → ℂ, {Y | 0 ≤ star v ⬝ᵥ (Y *ᵥ v)} := by
    ext Y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [this]
  refine IsClosed.inter (isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id)
    (isClosed_iInter fun v => ?_)
  refine isClosed_le continuous_const ?_
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

lemma g72gk1b_closed {d N M : ℕ} :
    IsClosed {c : g72gk1b_V d N M | IsBoseInputChannel (g72gk1b_rec c)} := by
  simp only [g72gk1b_K_iff, Set.setOf_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · have : {c : g72gk1b_V d N M | Entanglement.IsCompletelyPositive (g72gk1b_recL c)} =
        ⋂ r : ℕ, ⋂ X ∈ {X : Matrix (Fin r × Word N d) (Fin r × Word N d) ℂ | X.PosSemidef},
          (fun c => idTensorSuperop (g72gk1b_rec c) X) ⁻¹' {Y | Y.PosSemidef} := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Entanglement.IsCompletelyPositive]
      rfl
    rw [this]
    refine isClosed_iInter fun r => isClosed_biInter fun X _ => ?_
    refine IsClosed.preimage ?_ g72gk1b_psd_closed
    refine continuous_pi fun p => continuous_pi fun q => ?_
    simp only [idTensorSuperop, Matrix.of_apply]
    exact g72gk1b_cont _ _ _
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun A => isClosed_eq (g72gk1b_contM A) (g72gk1b_contM _)
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun A => isClosed_eq (g72gk1b_contM A).matrix_trace continuous_const

def g72gk1b_pv {d N : ℕ} (x y : Word N d) (k : Fin 4) : EuclideanSpace ℂ (Word N d) :=
  WithLp.toLp 2 (Pi.single x 1 + Pi.single y (Complex.I ^ (k : ℕ)))

lemma g72gk1b_polar {d N : ℕ} (x y : Word N d) :
    (Matrix.single x y 1 : TensorMat d N) =
      ∑ k : Fin 4, (Complex.I ^ (k : ℕ) / 4) • pureDensity (g72gk1b_pv x y k) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pureDensity, Matrix.of_apply, g72gk1b_pv,
    PiLp.toLp_apply, Pi.add_apply, Pi.single_apply, Matrix.single_apply, Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, map_add, apply_ite (starRingEnd ℂ), map_one, map_zero]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
  have hc : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
  simp only [pow_zero, pow_one, hI2, hI3, map_neg, hc, map_one]
  by_cases hxy : x = y
  · subst hxy
    by_cases hax : a = x <;> by_cases hbx : b = x <;>
      simp [hax, hbx] <;> (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring_nf) <;>
      (try exact fun h => by simp_all)
  · by_cases hax : a = x <;> by_cases hay : a = y <;> by_cases hbx : b = x <;> by_cases hby : b = y <;>
      simp [hax, hay, hbx, hby, hxy, Ne.symm hxy] <;> (try ring_nf) <;> (try simp [Complex.I_sq]) <;>
      (try ring_nf) <;> (try exact fun h => by simp_all) <;> simp_all

def g72gk1b_R {d N : ℕ} (x y : Word N d) : ℝ :=
  ∑ k : Fin 4, (1 / 4) * (2 * ‖(boseProjector d N * pureDensity (g72gk1b_pv x y k) * boseProjector d N).trace‖)

lemma g72gk1b_bound {d N M : ℕ} (c : g72gk1b_V d N M) (hc : IsBoseInputChannel (g72gk1b_rec c))
    (x y : Word N d) (i j : Word M d) : ‖c x y i j‖ ≤ g72gk1b_R x y := by
  rw [← g72gk1b_rec_single c x y i j, g72gk1b_polar]
  have hlin : g72gk1b_rec c (∑ k : Fin 4, (Complex.I ^ (k : ℕ) / 4) • pureDensity (g72gk1b_pv x y k)) =
      ∑ k : Fin 4, (Complex.I ^ (k : ℕ) / 4) • g72gk1b_rec c (pureDensity (g72gk1b_pv x y k)) := by
    change g72gk1b_recL c _ = ∑ k : Fin 4, (Complex.I ^ (k : ℕ) / 4) • g72gk1b_recL c _
    rw [map_sum]; simp only [map_smul]
  rw [hlin, Matrix.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  have hk : ‖Complex.I ^ (k : ℕ) / 4‖ = 1 / 4 := by simp [norm_pow, Complex.norm_I]
  rw [hk]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hpsd := g72gk1_out_psd _ hc _ (g72gk1_pure_psd (g72gk1b_pv x y k))
  have := g72gk1b_psd_entry _ hpsd i j
  rwa [hc.2.2] at this

lemma g72gk1b_compact {d N M : ℕ} :
    IsCompact {c : g72gk1b_V d N M | IsBoseInputChannel (g72gk1b_rec c)} := by
  have hK : IsCompact (Set.pi Set.univ fun x : Word N d => Set.pi Set.univ fun y : Word N d =>
      Set.pi Set.univ fun i : Word M d => Set.pi Set.univ fun j : Word M d =>
        Metric.closedBall (0 : ℂ) (g72gk1b_R x y)) :=
    isCompact_univ_pi fun x => isCompact_univ_pi fun y => isCompact_univ_pi fun i =>
      isCompact_univ_pi fun j => isCompact_closedBall _ _
  refine hK.of_isClosed_subset g72gk1b_closed ?_
  intro c hc
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun x y i j => g72gk1b_bound c hc x y i j

lemma g72gk1b_ov_cont {d N M : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
    Continuous fun c : g72gk1b_V d N M => cloningOverlap (g72gk1b_rec c) phi := by
  unfold cloningOverlap
  exact Complex.continuous_re.comp ((continuous_const.matrix_mul (g72gk1b_contM _)).matrix_trace)

lemma g72gk1b_can_bic {d N M : ℕ} (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M) :
    IsBoseInputChannel (canonicalCloner (d := d) hNM.le) := by
  have hPAP : ∀ A : TensorMat d N, canonicalCloner (d := d) hNM.le A =
      canonicalCloner hNM.le (boseProjector d N * A * boseProjector d N) := by
    intro A
    unfold canonicalCloner
    simp only [← Matrix.mul_assoc, g72gk1_m_PP]
    simp only [Matrix.mul_assoc, g72gk1_m_PP]
  have hPAPb : ∀ A : TensorMat d N, BoseSupported (boseProjector d N * A * boseProjector d N) := by
    intro A; constructor
    · simp only [← Matrix.mul_assoc, g72gk1_m_PP]
    · simp only [Matrix.mul_assoc, g72gk1_m_PP]
  refine ⟨⟨g72gk1_o_Lmap hNM.le, fun A => g72gk1_o_kraus_eq hNM.le A, g72gk1_o_cp hNM.le⟩, hPAP, fun A => ?_⟩
  rw [hPAP]
  exact g72gk1_o_bc_trace hd hN (by omega) _ _ (g72gk1_o_bc_all hd hN M hNM.le) _ (hPAPb A)

theorem solution (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M) :
    (∀ T : CloneMap d N M, IsBoseInputChannel T → cloningFidelity T ∈ Set.Icc (0 : ℝ) 1) ∧
    ∃ T : CloneMap d N M, IsBoseInputChannel T ∧ cloningFidelity T = optimalFidelity d N M ∧
      ∀ S : CloneMap d N M, IsBoseInputChannel S → cloningFidelity S ≤ cloningFidelity T := by
  obtain ⟨phi0, hphi0⟩ := g72gk1_unit_exists hd
  refine ⟨fun T hT => ⟨le_csInf ⟨_, phi0, hphi0, rfl⟩ (by
    rintro r ⟨ψ, hψ, rfl⟩; exact (g72gk1_ov_bounds T hT ψ hψ).1), g72gk1_fid_le_one hd T hT⟩, ?_⟩
  set W := {r : ℝ | ∃ T : CloneMap d N M, IsBoseInputChannel T ∧ r = cloningFidelity T} with hW
  have hne : W.Nonempty := ⟨_, canonicalCloner hNM.le, g72gk1b_can_bic hd hN hNM, rfl⟩
  have hbdd : BddAbove W := ⟨1, by rintro r ⟨T, hT, rfl⟩; exact g72gk1_fid_le_one hd T hT⟩
  obtain ⟨u, -, hlim, hmem⟩ := exists_seq_tendsto_sSup hne hbdd
  choose T hT hu using hmem
  have hrec : ∀ n, g72gk1b_rec (g72gk1b_coef (T n)) = T n := by
    intro n
    obtain ⟨⟨L, hTL, -⟩, -, -⟩ := hT n
    exact g72gk1b_rec_coef (T n) L hTL
  have hcK : ∀ n, g72gk1b_coef (T n) ∈ {c : g72gk1b_V d N M | IsBoseInputChannel (g72gk1b_rec c)} := by
    intro n; show IsBoseInputChannel _; rw [hrec n]; exact hT n
  obtain ⟨c0, hc0, φs, hφs, hlimc⟩ := g72gk1b_compact.tendsto_subseq hcK
  have hT0 : IsBoseInputChannel (g72gk1b_rec c0) := hc0
  have hle : sSup W ≤ cloningFidelity (g72gk1b_rec c0) := by
    refine le_csInf ⟨_, phi0, hphi0, rfl⟩ ?_
    rintro r ⟨ψ, hψ, rfl⟩
    have hconv : Filter.Tendsto (fun n => cloningOverlap (g72gk1b_rec (g72gk1b_coef (T (φs n)))) ψ)
        Filter.atTop (nhds (cloningOverlap (g72gk1b_rec c0) ψ)) :=
      ((g72gk1b_ov_cont ψ).tendsto c0).comp hlimc
    have hu' : Filter.Tendsto (u ∘ φs) Filter.atTop (nhds (sSup W)) := hlim.comp hφs.tendsto_atTop
    refine le_of_tendsto_of_tendsto' hu' hconv fun n => ?_
    simp only [Function.comp_apply, hrec]
    rw [hu]
    exact g72gk1_fid_le _ (hT _) ψ hψ
  have hge : cloningFidelity (g72gk1b_rec c0) ≤ sSup W := le_csSup hbdd ⟨_, hT0, rfl⟩
  refine ⟨g72gk1b_rec c0, hT0, le_antisymm hge hle, fun S hS => ?_⟩
  exact (le_csSup hbdd ⟨S, hS, rfl⟩).trans hle
