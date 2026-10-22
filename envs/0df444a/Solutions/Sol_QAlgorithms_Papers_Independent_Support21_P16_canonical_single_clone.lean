-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P16.canonical_single_clone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:19:47.813777+00:00
-- url     : https://prove2.me/submissions/ecf83edc-449a-40ba-a119-89247569f9d5

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



lemma g66m2_tP_mul {d n : ℕ} (s t : Equiv.Perm (Fin n)) :
    Schur.tensorPermutation d n s * Schur.tensorPermutation d n t = Schur.tensorPermutation d n (s * t) := by
  ext y x
  simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (x ∘ t.symm)]
  · simp only [if_true]
    congr 1
  · intro b _ hb; simp [hb]
  · simp

lemma g66m2_P_tP {d n : ℕ} (t : Equiv.Perm (Fin n)) :
    boseProjector d n * Schur.tensorPermutation d n t = boseProjector d n := by
  rw [boseProjector, Matrix.smul_mul, Finset.sum_mul]
  simp only [g66m2_tP_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight t) _ _ (fun _ => rfl)

lemma g66m2_tP_P {d n : ℕ} (t : Equiv.Perm (Fin n)) :
    Schur.tensorPermutation d n t * boseProjector d n = boseProjector d n := by
  rw [boseProjector, Matrix.mul_smul, Finset.mul_sum]
  simp only [g66m2_tP_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft t) _ _ (fun _ => rfl)

lemma g66m2_PP {d n : ℕ} : boseProjector d n * boseProjector d n = boseProjector d n := by
  nth_rewrite 1 [boseProjector]
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp only [g66m2_tP_P, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin n))).ne'), one_smul]

lemma g66m2_prod_delta {d N M : ℕ} (h : N ≤ M) (x y : Word M d) :
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

lemma g66m2_tWI_apply {d N M : ℕ} (h : N ≤ M) (A : TensorMat d N) (x y : Word M d) :
    tensorWithIdentity h A x y = A (fun k => x ⟨k.val, by omega⟩) (fun k => y ⟨k.val, by omega⟩) *
      if (∀ j : Fin M, N ≤ j.val → x j = y j) then 1 else 0 := by
  rw [tensorWithIdentity, g66m2_prod_delta h]

lemma g66m2_tWI_tWI {d N M R : ℕ} (h1 : N ≤ M) (h2 : M ≤ R) (A : TensorMat d N) :
    tensorWithIdentity h2 (tensorWithIdentity h1 A) = tensorWithIdentity (h1.trans h2) A := by
  ext x y
  rw [g66m2_tWI_apply, g66m2_tWI_apply, g66m2_tWI_apply]
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

def g66m2_split {d N M : ℕ} (h : N ≤ M) : Word M d ≃ Word N d × Word (M - N) d where
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

lemma g66m2_tWI_mul {d N M : ℕ} (h : N ≤ M) (A B : TensorMat d N) :
    tensorWithIdentity h (A * B) = tensorWithIdentity h A * tensorWithIdentity h B := by
  ext x y
  rw [Matrix.mul_apply, ← (g66m2_split h).symm.sum_comp, Fintype.sum_prod_type]
  simp only [g66m2_tWI_apply, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_eq_single (g66m2_split h x).2]
  · have e1 : (fun k : Fin N => (g66m2_split h).symm (u, (g66m2_split h x).2) ⟨k.val, by omega⟩) = u := by
      ext k; simp [g66m2_split]
    have hx : ∀ j : Fin M, N ≤ j.val → x j = (g66m2_split h).symm (u, (g66m2_split h x).2) j := by
      intro j hj
      simp only [g66m2_split, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, dif_neg (show ¬ j.val < N by omega)]
      congr 1; ext; simp; omega
    rw [e1, if_pos hx]
    by_cases H : ∀ j : Fin M, N ≤ j.val → x j = y j
    · rw [if_pos H, if_pos (fun j hj => (hx j hj).symm.trans (H j hj))]; ring
    · rw [if_neg H, if_neg (fun H' => H (fun j hj => (hx j hj).trans (H' j hj)))]; ring
  · intro v _ hv
    have : ¬ ∀ j : Fin M, N ≤ j.val → x j = (g66m2_split h).symm (u, v) j := by
      intro H; apply hv; ext k
      have := H ⟨N + k.val, by omega⟩ (by simp)
      simp only [g66m2_split, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk] at this ⊢
      rw [this, dif_neg (by simp)]; congr 1; ext; simp
    rw [if_neg this]; ring
  · simp

lemma g66m2_tWI_smul {d N M : ℕ} (h : N ≤ M) (c : ℂ) (A : TensorMat d N) :
    tensorWithIdentity h (c • A) = c • tensorWithIdentity h A := by
  ext x y; simp only [g66m2_tWI_apply, Matrix.smul_apply, smul_eq_mul]; ring

lemma g66m2_tWI_sum {d N M : ℕ} (h : N ≤ M) {ι : Type*} (s : Finset ι) (A : ι → TensorMat d N) :
    tensorWithIdentity h (∑ i ∈ s, A i) = ∑ i ∈ s, tensorWithIdentity h (A i) := by
  ext x y; simp only [g66m2_tWI_apply, Matrix.sum_apply, Finset.sum_mul]

def g66m2_emb {M R : ℕ} (h : M ≤ R) : Fin M ≃ {k : Fin R // k.val < M} where
  toFun i := ⟨⟨i.val, by omega⟩, i.2⟩
  invFun k := ⟨k.1.val, k.2⟩
  left_inv i := rfl
  right_inv k := rfl

def g66m2_ext {M R : ℕ} (h : M ≤ R) (t : Equiv.Perm (Fin M)) : Equiv.Perm (Fin R) :=
  t.extendDomain (g66m2_emb h)

lemma g66m2_ext_symm_lt {M R : ℕ} (h : M ≤ R) (t : Equiv.Perm (Fin M)) (j : Fin R) (hj : j.val < M) :
    (g66m2_ext h t).symm j = ⟨(t.symm ⟨j.val, hj⟩).val, by omega⟩ := by
  have e : (g66m2_ext h t).symm = g66m2_ext h t⁻¹ := by
    rw [g66m2_ext, g66m2_ext, ← Equiv.Perm.extendDomain_inv]; rfl
  rw [e, g66m2_ext, Equiv.Perm.extendDomain_apply_subtype (b := j) _ _ hj]
  rfl

lemma g66m2_ext_symm_ge {M R : ℕ} (h : M ≤ R) (t : Equiv.Perm (Fin M)) (j : Fin R) (hj : ¬ j.val < M) :
    (g66m2_ext h t).symm j = j := by
  have e : (g66m2_ext h t).symm = g66m2_ext h t⁻¹ := by
    rw [g66m2_ext, g66m2_ext, ← Equiv.Perm.extendDomain_inv]; rfl
  rw [e, g66m2_ext, Equiv.Perm.extendDomain_apply_not_subtype (b := j) _ _ hj]

lemma g66m2_tWI_tP {d M R : ℕ} (h : M ≤ R) (t : Equiv.Perm (Fin M)) :
    tensorWithIdentity h (Schur.tensorPermutation d M t) =
      Schur.tensorPermutation d R (g66m2_ext h t) := by
  ext x y
  rw [g66m2_tWI_apply]
  simp only [Schur.tensorPermutation, Matrix.of_apply, ite_zero_mul_ite_zero, mul_one]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    funext j
    simp only [Function.comp_apply]
    by_cases hj : j.val < M
    · rw [g66m2_ext_symm_lt h t j hj]
      have := congrFun h1 ⟨j.val, hj⟩
      simpa using this
    · rw [g66m2_ext_symm_ge h t j hj]; exact h2 j (by omega)
  · intro H
    refine ⟨?_, fun j hj => ?_⟩
    · funext k
      have := congrFun H ⟨k.val, by omega⟩
      simp only [Function.comp_apply] at this ⊢
      rw [this, g66m2_ext_symm_lt h t _ k.2]
    · have := congrFun H j
      simp only [Function.comp_apply] at this
      rw [this, g66m2_ext_symm_ge h t j (by omega)]

lemma g66m2_absorb_l {d M R : ℕ} (h : M ≤ R) :
    boseProjector d R * tensorWithIdentity h (boseProjector d M) = boseProjector d R := by
  rw [show boseProjector d M = ((Fintype.card (Equiv.Perm (Fin M)) : ℂ)⁻¹) •
      ∑ p, Schur.tensorPermutation d M p from rfl, g66m2_tWI_smul, g66m2_tWI_sum, Matrix.mul_smul, Finset.mul_sum]
  simp only [g66m2_tWI_tP, g66m2_P_tP, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin M))).ne'), one_smul]

lemma g66m2_absorb_r {d M R : ℕ} (h : M ≤ R) :
    tensorWithIdentity h (boseProjector d M) * boseProjector d R = boseProjector d R := by
  rw [show boseProjector d M = ((Fintype.card (Equiv.Perm (Fin M)) : ℂ)⁻¹) •
      ∑ p, Schur.tensorPermutation d M p from rfl, g66m2_tWI_smul, g66m2_tWI_sum, Matrix.smul_mul, Finset.sum_mul]
  simp only [g66m2_tWI_tP, g66m2_tP_P, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin M))).ne'), one_smul]

lemma g66m2_boseDim_pos (d M : ℕ) (hd : 0 < d) : 0 < boseDimension d M := by
  unfold boseDimension; exact Nat.choose_pos (by omega)

/-- Part (a) of canonical_concatenation. -/
lemma g66m2_concat (d N M R : ℕ) (hd : 0 < d) (hNM : N ≤ M) (hMR : M ≤ R) :
    (canonicalCloner (d := d) hMR ∘ canonicalCloner hNM) = canonicalCloner (hNM.trans hMR) := by
  funext A
  simp only [Function.comp_apply, canonicalCloner]
  set W := tensorWithIdentity hNM (boseProjector d N * A * boseProjector d N)
  set c1 : ℂ := (boseDimension d N : ℂ) / (boseDimension d M : ℂ)
  have h1 : boseProjector d M * (c1 • (boseProjector d M * W * boseProjector d M)) * boseProjector d M =
      c1 • (boseProjector d M * W * boseProjector d M) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]; congr 1
    simp only [← Matrix.mul_assoc, g66m2_PP]
    simp only [Matrix.mul_assoc, g66m2_PP]
  rw [h1, g66m2_tWI_smul, g66m2_tWI_mul, g66m2_tWI_mul, g66m2_tWI_tWI, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul]
  have hM : (boseDimension d M : ℂ) ≠ 0 := by exact_mod_cast (g66m2_boseDim_pos d M hd).ne'
  have hc : (boseDimension d M : ℂ) / (boseDimension d R : ℂ) * c1 =
      (boseDimension d N : ℂ) / (boseDimension d R : ℂ) := by
    simp only [c1]; field_simp
  rw [hc]; congr 1
  simp only [← Matrix.mul_assoc, g66m2_absorb_l]
  simp only [Matrix.mul_assoc, g66m2_absorb_r]

/-- Part (b) of canonical_concatenation. -/
lemma g66m2_coef (d N M : ℕ) (hNM : N < M) :
    canonicalCoefficient d N M = coefficientFactor d N / coefficientFactor d M := by
  unfold canonicalCoefficient coefficientFactor
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hdM : (0 : ℝ) < d + M := by positivity
  field_simp

/-! ### g68o: site reductions and Bose invariance -/

lemma g68o_tPA {d n : ℕ} (σ : Equiv.Perm (Fin n)) (A : TensorMat d n) (x y : Word n d) :
    (Schur.tensorPermutation d n σ * A) x y = A (x ∘ σ) y := by
  simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (x ∘ σ)]
  · rw [if_pos (by ext k; simp)]
  · intro b _ hb; rw [if_neg]; intro h; apply hb; rw [h]; ext k; simp
  · simp

lemma g68o_AtP {d n : ℕ} (σ : Equiv.Perm (Fin n)) (A : TensorMat d n) (x y : Word n d) :
    (A * Schur.tensorPermutation d n σ) x y = A x (y ∘ σ.symm) := by
  simp only [Matrix.mul_apply, Schur.tensorPermutation, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (y ∘ σ.symm)]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg hb]
  · simp

lemma g68o_linv {d n : ℕ} {A : TensorMat d n} (h : boseProjector d n * A = A)
    (σ : Equiv.Perm (Fin n)) (x y : Word n d) : A (x ∘ σ) y = A x y := by
  have h1 : Schur.tensorPermutation d n σ * A = A := by
    rw [← h, ← Matrix.mul_assoc, g66m2_tP_P]
  rw [← g68o_tPA σ A x y, h1]

lemma g68o_rinv {d n : ℕ} {A : TensorMat d n} (h : A * boseProjector d n = A)
    (σ : Equiv.Perm (Fin n)) (x y : Word n d) : A x (y ∘ σ) = A x y := by
  have h1 : A * Schur.tensorPermutation d n σ.symm = A := by
    rw [← h, Matrix.mul_assoc, g66m2_P_tP]
  have := g68o_AtP σ.symm A x y
  rw [h1, Equiv.symm_symm] at this
  exact this.symm

/-- site reduction in update form -/
def g68o_R {d n : ℕ} (i : Fin n) (X : TensorMat d n) : Matrix (Fin d) (Fin d) ℂ :=
  fun a b => ∑ x : Word n d, if x i = a then X x (Function.update x i b) else 0

def g68o_pe {d n : ℕ} (σ : Equiv.Perm (Fin n)) : Word n d ≃ Word n d where
  toFun y := y ∘ σ
  invFun y := y ∘ σ.symm
  left_inv y := by ext; simp
  right_inv y := by ext; simp

lemma g68o_R_swap {d n : ℕ} {X : TensorMat d n}
    (hX : ∀ σ : Equiv.Perm (Fin n), ∀ x y, X (x ∘ σ) (y ∘ σ) = X x y) (i j : Fin n) :
    g68o_R i X = g68o_R j X := by
  ext a b
  unfold g68o_R
  rw [← (g68o_pe (d := d) (Equiv.swap i j)).sum_comp]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp only [g68o_pe, Equiv.coe_fn_mk, Function.comp_apply, Equiv.swap_apply_left]
  congr 1
  have : Function.update (y ∘ Equiv.swap i j) i b = Function.update y j b ∘ Equiv.swap i j := by
    have := Function.update_comp_equiv y (Equiv.swap i j) j b
    rw [Equiv.symm_swap, Equiv.swap_apply_right] at this
    exact this.symm
  rw [this, hX]

lemma g68o_K {d n : ℕ} (i : Fin n) (G : Word n d → ℂ) (f : Word n d → Fin d)
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

lemma g68o_K_all {d n : ℕ} (i : Fin n) (G : Word n d → ℂ)
    (hG : ∀ w c, G (Function.update w i c) = G w) (a : Fin d) :
    (∑ w : Word n d, G w) = (d : ℂ) * ∑ w : Word n d, if w i = a then G w else 0 := by
  have : (∑ w : Word n d, G w) = ∑ c : Fin d, ∑ w : Word n d, if w i = c then G w else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.sum_ite_eq]; simp
  rw [this]
  have h2 : ∀ c : Fin d, (∑ w : Word n d, if w i = c then G w else 0) =
      ∑ w : Word n d, if w i = a then G w else 0 := fun c =>
    g68o_K i G (fun _ => c) hG (fun _ _ => rfl) a
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

def g68o_pre {d n : ℕ} (hn : 1 ≤ n) : Fin d × Word (n - 1) d ≃ Word n d where
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

lemma g68o_oneSite_R {d n : ℕ} (hn : 1 ≤ n) (X : TensorMat d n) :
    oneSite hn X = g68o_R ⟨0, by omega⟩ X := by
  ext a b
  unfold oneSite g68o_R
  rw [← (g68o_pre (d := d) hn).sum_comp, Fintype.sum_prod_type]
  simp only [g68o_pre, Equiv.coe_fn_mk]
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

lemma g68o_trace_R {d n : ℕ} (i : Fin n) (X : TensorMat d n) :
    (g68o_R i X).trace = X.trace := by
  unfold g68o_R Matrix.trace
  simp only [Matrix.diag]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_ite_eq]; simp

lemma g68o_trace_oneSite {d n : ℕ} (hn : 1 ≤ n) (X : TensorMat d n) :
    (oneSite hn X).trace = X.trace := by
  rw [g68o_oneSite_R, g68o_trace_R]

/-! ### g68o: coset decomposition of the Bose projector -/

lemma g68o_ext_last (N : ℕ) (π : Equiv.Perm (Fin N)) :
    g66m2_ext (Nat.le_succ N) π (Fin.last N) = Fin.last N := by
  have := g66m2_ext_symm_ge (Nat.le_succ N) π (Fin.last N) (by simp)
  exact ((Equiv.symm_apply_eq _).mp this).symm

lemma g68o_ext_inj (N : ℕ) {π π' : Equiv.Perm (Fin N)}
    (h : g66m2_ext (Nat.le_succ N) π = g66m2_ext (Nat.le_succ N) π') : π = π' :=
  Equiv.Perm.extendDomainHom_injective (g66m2_emb (Nat.le_succ N)) h

lemma g68o_card (N : ℕ) : Fintype.card (Fin (N+1) × Equiv.Perm (Fin N)) =
    Fintype.card (Equiv.Perm (Fin (N+1))) := by
  simp [Fintype.card_perm, Nat.factorial_succ]

lemma g68o_phi_bij (N : ℕ) : Function.Bijective
    (fun p : Fin (N+1) × Equiv.Perm (Fin N) => Equiv.swap p.1 (Fin.last N) * g66m2_ext (Nat.le_succ N) p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, g68o_card N⟩
  rintro ⟨k, π⟩ ⟨k', π'⟩ h
  simp only at h
  have hk : k = k' := by
    have := congrArg (fun σ : Equiv.Perm (Fin (N+1)) => σ (Fin.last N)) h
    simpa [Equiv.Perm.mul_apply, g68o_ext_last] using this
  subst hk
  rw [g68o_ext_inj N (mul_left_cancel h)]

lemma g68o_psi_bij (N : ℕ) : Function.Bijective
    (fun p : Fin (N+1) × Equiv.Perm (Fin N) => g66m2_ext (Nat.le_succ N) p.2 * Equiv.swap p.1 (Fin.last N)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, g68o_card N⟩
  rintro ⟨k, π⟩ ⟨k', π'⟩ h
  simp only at h
  have hk : k = k' := by
    have h1 : (g66m2_ext (Nat.le_succ N) π * Equiv.swap k (Fin.last N)) k = Fin.last N := by
      simp [Equiv.Perm.mul_apply, g68o_ext_last]
    have h2 : (g66m2_ext (Nat.le_succ N) π * Equiv.swap k (Fin.last N)) k' = Fin.last N := by
      rw [h]; simp [Equiv.Perm.mul_apply, g68o_ext_last]
    exact (g66m2_ext (Nat.le_succ N) π * Equiv.swap k (Fin.last N)).injective (h1.trans h2.symm)
  subst hk
  rw [g68o_ext_inj N (mul_right_cancel h)]

lemma g68o_sumP (d N : ℕ) : ∑ π : Equiv.Perm (Fin N), Schur.tensorPermutation d (N+1) (g66m2_ext (Nat.le_succ N) π) =
    ((Nat.factorial N : ℕ) : ℂ) • tensorWithIdentity (Nat.le_succ N) (boseProjector d N) := by
  rw [show boseProjector d N = ((Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹) •
      ∑ p, Schur.tensorPermutation d N p from rfl, g66m2_tWI_smul, g66m2_tWI_sum, smul_smul]
  simp only [g66m2_tWI_tP, Fintype.card_perm, Fintype.card_fin]
  rw [mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_pos N).ne'), one_smul]

lemma g68o_Pdec_l (d N : ℕ) : boseProjector d (N+1) = ((N + 1 : ℂ))⁻¹ •
    ∑ k : Fin (N+1), Schur.tensorPermutation d (N+1) (Equiv.swap k (Fin.last N)) *
      tensorWithIdentity (Nat.le_succ N) (boseProjector d N) := by
  rw [show boseProjector d (N+1) = ((Fintype.card (Equiv.Perm (Fin (N+1))) : ℂ)⁻¹) •
      ∑ p, Schur.tensorPermutation d (N+1) p from rfl]
  rw [← Fintype.sum_bijective _ (g68o_phi_bij N) (fun p => Schur.tensorPermutation d (N+1)
    (Equiv.swap p.1 (Fin.last N) * g66m2_ext (Nat.le_succ N) p.2)) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [← g66m2_tP_mul, ← Finset.mul_sum, g68o_sumP, Matrix.mul_smul, ← Finset.smul_sum, smul_smul]
  congr 1
  simp only [Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]
  have : ((Nat.factorial N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  push_cast
  field_simp

lemma g68o_Pdec_r (d N : ℕ) : boseProjector d (N+1) = ((N + 1 : ℂ))⁻¹ •
    ∑ k : Fin (N+1), tensorWithIdentity (Nat.le_succ N) (boseProjector d N) *
      Schur.tensorPermutation d (N+1) (Equiv.swap k (Fin.last N)) := by
  rw [show boseProjector d (N+1) = ((Fintype.card (Equiv.Perm (Fin (N+1))) : ℂ)⁻¹) •
      ∑ p, Schur.tensorPermutation d (N+1) p from rfl]
  rw [← Fintype.sum_bijective _ (g68o_psi_bij N) (fun p => Schur.tensorPermutation d (N+1)
    (g66m2_ext (Nat.le_succ N) p.2 * Equiv.swap p.1 (Fin.last N))) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [← g66m2_tP_mul, ← Finset.sum_mul, g68o_sumP, Matrix.smul_mul, ← Finset.smul_sum, smul_smul]
  congr 1
  simp only [Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]
  have : ((Nat.factorial N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  push_cast
  field_simp

lemma g68o_tPBtP {d n : ℕ} (s t : Equiv.Perm (Fin n)) (B : TensorMat d n) (x y : Word n d) :
    (Schur.tensorPermutation d n s * B * Schur.tensorPermutation d n t) x y = B (x ∘ s) (y ∘ t.symm) := by
  rw [g68o_AtP, g68o_tPA]

lemma g68o_X_entry {d N : ℕ} (A : TensorMat d N) (hL : boseProjector d N * A = A)
    (hR : A * boseProjector d N = A) (x y : Word (N+1) d) :
    (boseProjector d (N+1) * tensorWithIdentity (Nat.le_succ N) A * boseProjector d (N+1)) x y =
      ((N + 1 : ℂ))⁻¹ ^ 2 * ∑ k : Fin (N+1), ∑ l : Fin (N+1),
        tensorWithIdentity (Nat.le_succ N) A (x ∘ Equiv.swap k (Fin.last N)) (y ∘ Equiv.swap l (Fin.last N)) := by
  have hA' : tensorWithIdentity (Nat.le_succ N) (boseProjector d N) * tensorWithIdentity (Nat.le_succ N) A *
      tensorWithIdentity (Nat.le_succ N) (boseProjector d N) = tensorWithIdentity (Nat.le_succ N) A := by
    rw [← g66m2_tWI_mul, ← g66m2_tWI_mul, hL, hR]
  have key : boseProjector d (N+1) * tensorWithIdentity (Nat.le_succ N) A * boseProjector d (N+1) =
      ((N + 1 : ℂ))⁻¹ ^ 2 • ∑ k : Fin (N+1), ∑ l : Fin (N+1),
        Schur.tensorPermutation d (N+1) (Equiv.swap k (Fin.last N)) * tensorWithIdentity (Nat.le_succ N) A *
          Schur.tensorPermutation d (N+1) (Equiv.swap l (Fin.last N)) := by
    nth_rewrite 1 [g68o_Pdec_l]
    rw [g68o_Pdec_r]
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
  simp only [Matrix.sum_apply, g68o_tPBtP, Equiv.symm_swap]

lemma g68o_snoc_last {d N : ℕ} (w : Word N d) (c : Fin d) :
    (Fin.snoc w c : Word (N+1) d) ∘ Equiv.swap (Fin.last N) (Fin.last N) = Fin.snoc w c := by
  rw [Equiv.swap_self]; rfl

lemma g68o_snoc_cs {d N : ℕ} (w : Word N d) (c : Fin d) (k : Fin N) :
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

lemma g68o_tWI_snoc {d N : ℕ} (A : TensorMat d N) (u v : Word N d) (c c' : Fin d) :
    tensorWithIdentity (Nat.le_succ N) A (Fin.snoc u c : Word (N+1) d) (Fin.snoc v c') =
      A u v * if c = c' then 1 else 0 := by
  rw [g66m2_tWI_apply]
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

lemma g68o_hX {d n : ℕ} {A : TensorMat d n} (hL : boseProjector d n * A = A)
    (hR : A * boseProjector d n = A) :
    ∀ σ : Equiv.Perm (Fin n), ∀ x y, A (x ∘ σ) (y ∘ σ) = A x y := by
  intro σ x y; rw [g68o_linv hL, g68o_rinv hR]

lemma g68o_Rlast_snoc {d N : ℕ} (X : TensorMat d (N+1)) (a b : Fin d) :
    g68o_R (Fin.last N) X a b = ∑ w : Word N d, X (Fin.snoc w a) (Fin.snoc w b) := by
  unfold g68o_R
  rw [← (Fin.snocEquiv (fun _ => Fin d)).sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    simp [Fin.snocEquiv, Fin.update_snoc_last]
  · intro c _ hc
    refine Finset.sum_eq_zero (fun w _ => ?_)
    simp [Fin.snocEquiv, hc]
  · simp

lemma g68o_Llc {d N : ℕ} (hN : 1 ≤ N) {A : TensorMat d N} (hL : boseProjector d N * A = A)
    (hR : A * boseProjector d N = A) (a b : Fin d) :
    (∑ w : Word N d, ∑ j : Fin N, A w (Function.update w j b) * (if a = w j then 1 else 0)) =
      (N : ℂ) * g68o_R ⟨0, by omega⟩ A a b := by
  rw [Finset.sum_comm]
  have : ∀ j : Fin N, (∑ w : Word N d, A w (Function.update w j b) * (if a = w j then 1 else 0)) =
      g68o_R ⟨0, by omega⟩ A a b := by
    intro j
    rw [← g68o_R_swap (g68o_hX hL hR) j]
    unfold g68o_R
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases h : w j = a
    · rw [if_pos h.symm, if_pos h, mul_one]
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma g68o_Lcl {d N : ℕ} (hN : 1 ≤ N) {A : TensorMat d N} (hL : boseProjector d N * A = A)
    (hR : A * boseProjector d N = A) (a b : Fin d) :
    (∑ w : Word N d, ∑ i : Fin N, A (Function.update w i a) w * (if w i = b then 1 else 0)) =
      (N : ℂ) * g68o_R ⟨0, by omega⟩ A a b := by
  rw [Finset.sum_comm]
  have : ∀ i : Fin N, (∑ w : Word N d, A (Function.update w i a) w * (if w i = b then 1 else 0)) =
      g68o_R ⟨0, by omega⟩ A a b := by
    intro i
    rw [← g68o_R_swap (g68o_hX hL hR) i]
    unfold g68o_R
    have e1 : ∀ w : Word N d, A (Function.update w i a) w * (if w i = b then 1 else 0) =
        if w i = (fun _ => b) w then A (Function.update w i a) (Function.update w i b) else 0 := by
      intro w
      by_cases h : w i = b
      · rw [if_pos h, if_pos h, mul_one]; congr 1; rw [← h, Function.update_eq_self]
      · rw [if_neg h, if_neg h, mul_zero]
    simp only [e1]
    rw [g68o_K i (fun w => A (Function.update w i a) (Function.update w i b)) (fun _ => b)
      (fun w c => by simp only [Function.update_idem]) (fun _ _ => rfl) a]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases h : w i = a
    · rw [if_pos h, if_pos h]; congr 1; rw [← h, Function.update_eq_self]
    · rw [if_neg h, if_neg h]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma g68o_Lcc {d N : ℕ} (hN : 1 ≤ N) {A : TensorMat d N} (hL : boseProjector d N * A = A)
    (hR : A * boseProjector d N = A) (a b : Fin d) :
    (∑ w : Word N d, ∑ i : Fin N, ∑ j : Fin N,
      A (Function.update w i a) (Function.update w j b) * (if w i = w j then 1 else 0)) =
      (N : ℂ) * ((N : ℂ) + d - 1) * g68o_R ⟨0, by omega⟩ A a b := by
  set Q := g68o_R ⟨0, by omega⟩ A a b
  have hX := g68o_hX hL hR
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
      show _ = g68o_R ⟨0, by omega⟩ A a b
      rw [← g68o_R_swap hX i]
      unfold g68o_R
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
        rw [g68o_K_all i _ hG a, hRi]; ring
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
            rw [← hu, g68o_rinv hR]
          · rw [if_neg h, if_neg h, mul_zero]
        simp only [e1]
        rw [g68o_K i _ (fun w : Word N d => w j) hG
          (fun w c => by simp [Function.update_of_ne (Ne.symm hij)]) a, hRi]
    simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma g68o_Rlast {d N : ℕ} (hN : 1 ≤ N) (A : TensorMat d N) (hL : boseProjector d N * A = A)
    (hR : A * boseProjector d N = A) (a b : Fin d) :
    g68o_R (Fin.last N) (boseProjector d (N+1) * tensorWithIdentity (Nat.le_succ N) A *
      boseProjector d (N+1)) a b =
      ((N + 1 : ℂ))⁻¹ ^ 2 * ((if a = b then 1 else 0) * A.trace +
        (N : ℂ) * ((N : ℂ) + d + 1) * g68o_R ⟨0, by omega⟩ A a b) := by
  rw [g68o_Rlast_snoc]
  simp only [g68o_X_entry A hL hR, Fin.sum_univ_castSucc, g68o_snoc_cs, g68o_snoc_last, g68o_tWI_snoc]
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_add_distrib]
  rw [g68o_Lcc hN hL hR, g68o_Lcl hN hL hR, g68o_Llc hN hL hR]
  have : (∑ w : Word N d, A w w * (if a = b then 1 else 0)) = (if a = b then 1 else 0) * A.trace := by
    rw [Matrix.trace, ← Finset.sum_mul, mul_comm]; rfl
  rw [this]; ring

/-! ### g68o: Black Cow coefficient of the canonical cloner -/

lemma g68o_oneSite_smul {d n : ℕ} (hn : 1 ≤ n) (c : ℂ) (X : TensorMat d n) :
    oneSite hn (c • X) = c • oneSite hn X := by
  ext a b; simp [oneSite, Finset.mul_sum]

lemma g68o_bD_succ (d N : ℕ) (hd : 0 < d) :
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

lemma g68o_bose_out {d N M : ℕ} (h : N ≤ M) (A : TensorMat d N) :
    BoseSupported (canonicalCloner (d := d) h A) := by
  unfold canonicalCloner BoseSupported
  constructor
  · rw [Matrix.mul_smul]; congr 1; simp only [← Matrix.mul_assoc, g66m2_PP]
  · rw [Matrix.smul_mul]; congr 1; simp only [Matrix.mul_assoc, g66m2_PP]

lemma g68o_trace_oneMixed (d : ℕ) (hd : 0 < d) : (oneMixed d).trace = 1 := by
  unfold oneMixed
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

lemma g68o_bc_trace {d N M : ℕ} (hd : 0 < d) (hN : 1 ≤ N) (hM : 1 ≤ M) (T : CloneMap d N M) (g : ℝ)
    (hT : HasBlackCowCoefficient hN hM T g) (A : TensorMat d N) (hA : BoseSupported A) :
    (T A).trace = A.trace := by
  have := congrArg Matrix.trace (hT A hA)
  rw [g68o_trace_oneSite, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, g68o_trace_oneSite,
    g68o_trace_oneMixed d hd] at this
  rw [this]; simp only [smul_eq_mul]; push_cast; ring

lemma g68o_bc_comp {d N M R : ℕ} (hd : 0 < d) (hN : 1 ≤ N) (hM : 1 ≤ M) (hR : 1 ≤ R)
    (T : CloneMap d N M) (S : CloneMap d M R) (g1 g2 : ℝ)
    (hT : HasBlackCowCoefficient hN hM T g1) (hS : HasBlackCowCoefficient hM hR S g2)
    (hTB : ∀ A, BoseSupported A → BoseSupported (T A)) :
    HasBlackCowCoefficient hN hR (S ∘ T) (g2 * g1) := by
  intro A hA
  simp only [Function.comp_apply]
  rw [hS (T A) (hTB A hA), hT A hA, g68o_bc_trace hd hN hM T g1 hT A hA]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast; ring

lemma g68o_tWI_self {d N : ℕ} (h : N ≤ N) (A : TensorMat d N) : tensorWithIdentity h A = A := by
  ext x y
  rw [g66m2_tWI_apply]
  have : (∀ j : Fin N, N ≤ j.val → x j = y j) := fun j hj => absurd j.isLt (by omega)
  rw [if_pos this, mul_one]

lemma g68o_bc_base {d N : ℕ} (hN : 1 ≤ N) (hd : 0 < d) :
    HasBlackCowCoefficient hN hN (canonicalCloner (d := d) (le_refl N)) 1 := by
  intro A hA
  have hc : canonicalCloner (d := d) (le_refl N) A = A := by
    unfold canonicalCloner
    rw [g68o_tWI_self, hA.1, hA.2, hA.1, hA.2, div_self, one_smul]
    exact_mod_cast (g66m2_boseDim_pos d N hd).ne'
  rw [hc]; simp

lemma g68o_bc_step {d N : ℕ} (hd : 0 < d) (hN : 1 ≤ N) :
    HasBlackCowCoefficient hN (by omega : 1 ≤ N + 1) (canonicalCloner (d := d) (Nat.le_succ N))
      (coefficientFactor d N / coefficientFactor d (N+1)) := by
  intro A hA
  have hL := hA.1
  have hR := hA.2
  have hPAP : boseProjector d N * A * boseProjector d N = A := by rw [hL, hR]
  unfold canonicalCloner
  rw [hPAP, g68o_oneSite_smul]
  set X := boseProjector d (N+1) * tensorWithIdentity (Nat.le_succ N) A * boseProjector d (N+1) with hXdef
  have hXL : boseProjector d (N+1) * X = X := by simp only [hXdef, ← Matrix.mul_assoc, g66m2_PP]
  have hXR : X * boseProjector d (N+1) = X := by simp only [hXdef, Matrix.mul_assoc, g66m2_PP]
  rw [g68o_oneSite_R, g68o_R_swap (g68o_hX hXL hXR) _ (Fin.last N), g68o_oneSite_R hN]
  ext a b
  rw [Matrix.smul_apply, hXdef, g68o_Rlast hN A hL hR a b]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, oneMixed, Matrix.one_apply]
  have hb := g68o_bD_succ d N hd
  have hbN : (boseDimension d N : ℂ) ≠ 0 := by exact_mod_cast (g66m2_boseDim_pos d N hd).ne'
  have hbN1 : (boseDimension d (N+1) : ℂ) ≠ 0 := by exact_mod_cast (g66m2_boseDim_pos d (N+1) hd).ne'
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

lemma g68o_bc_all {d N : ℕ} (hd : 0 < d) (hN : 1 ≤ N) :
    ∀ M (h : N ≤ M), HasBlackCowCoefficient hN (by omega : 1 ≤ M) (canonicalCloner (d := d) h)
      (coefficientFactor d N / coefficientFactor d M) := by
  intro M h
  induction M, h using Nat.le_induction with
  | base =>
    have hf : coefficientFactor d N ≠ 0 := by
      unfold coefficientFactor
      have : (0 : ℝ) < N := by exact_mod_cast hN
      positivity
    rw [div_self hf]; exact g68o_bc_base hN hd
  | succ M hNM ih =>
    have hcomp := g66m2_concat d N M (M+1) hd hNM (Nat.le_succ M)
    rw [← hcomp]
    have hfM : coefficientFactor d M ≠ 0 := by
      unfold coefficientFactor
      have : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      positivity
    have := g68o_bc_comp hd hN (by omega) (by omega) _ _ _ _ ih (g68o_bc_step hd (show 1 ≤ M by omega))
      (fun A _ => g68o_bose_out hNM A)
    convert this using 1
    field_simp
lemma g66j_pvc {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (x : Word n d) :
    coherentTensor n phi x = ∏ k, phi (x k) := rfl

lemma g66j_PD {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
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
      simp only [g66j_pvc, Function.comp_apply]
      exact Equiv.prod_comp p (fun k => phi (y k))
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; rw [h]; ext k; simp
    · simp
  rw [boseProjector, Matrix.smul_mul, Finset.sum_mul]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin n))).ne'), one_smul]

lemma g66j_DP {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
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
      simp only [g66j_pvc, Function.comp_apply]
      exact Equiv.prod_comp p.symm (fun k => phi (z k))
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; rw [h]
    · simp
  rw [boseProjector, Matrix.mul_smul, Finset.mul_sum]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin n))).ne'), one_smul]
lemma g66j_norm1 {d n : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    ∑ u : Word n d, coherentTensor n phi u * conj (coherentTensor n phi u) = 1 := by
  simp only [g66j_pvc, map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin n) a => phi a * conj (phi a))]
  have : ∑ a, phi a * conj (phi a) = 1 := by
    have h2 : ‖phi‖ ^ 2 = 1 := by rw [hphi]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h2
    simp only [Complex.mul_conj']
    exact_mod_cast h2
  simp [this]

lemma g68o_coh_bose {d N : ℕ} (phi : EuclideanSpace ℂ (Fin d)) :
    BoseSupported (pureDensity (coherentTensor N phi)) := ⟨g66j_PD phi, g66j_DP phi⟩

lemma g68o_coh_trace {d N : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    (pureDensity (coherentTensor N phi)).trace = 1 := by
  rw [← g66j_norm1 (n := N) phi hphi]; rfl

lemma g68o_coh_oneSite {d N : ℕ} (hN : 1 ≤ N) (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    oneSite hN (pureDensity (coherentTensor N phi)) = pureDensity phi := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hv : ∀ (a : Fin d) (z : Word (n + 1 - 1) d),
      coherentTensor (n+1) phi (prependWord hN a z) = phi a * coherentTensor n phi z := by
    intro a z
    rw [g66j_pvc, g66j_pvc, Fin.prod_univ_succ]
    congr 1
  ext a b
  simp only [oneSite, pureDensity, Matrix.of_apply, hv, map_mul]
  have := g66j_norm1 (n := n) phi hphi
  calc _ = phi a * conj (phi b) * ∑ z : Word n d, coherentTensor n phi z * conj (coherentTensor n phi z) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => by ring)
    _ = _ := by rw [this, mul_one]

lemma g68o_rho_trace {d : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    (pureDensity phi).trace = 1 := by
  have := g66j_norm1 (n := 1) phi hphi
  simp only [g66j_pvc, Finset.univ_unique, Finset.prod_singleton] at this
  rw [← this, Matrix.trace]
  simp only [Matrix.diag, pureDensity, Matrix.of_apply]
  exact (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin d)).symm _ _ (fun _ => rfl))

lemma g68o_rho_idem {d : ℕ} (phi : EuclideanSpace ℂ (Fin d)) (hphi : ‖phi‖ = 1) :
    pureDensity phi * pureDensity phi = pureDensity phi := by
  have ht := g68o_rho_trace phi hphi
  simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply] at ht
  ext a c
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply]
  calc _ = phi a * conj (phi c) * ∑ b, phi b * conj (phi b) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)
    _ = _ := by rw [ht, mul_one]

theorem solution (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M) :
    HasBlackCowCoefficient hN (by omega) (canonicalCloner (d := d) hNM.le)
      (canonicalCoefficient d N M) ∧
    (∀ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 →
      ((QAlgorithms.pureDensity phi) *
        oneSite (by omega) (canonicalCloner hNM.le
          (QAlgorithms.pureDensity (coherentTensor N phi)))).trace.re =
      canonicalCoefficient d N M + (1 - canonicalCoefficient d N M) / d) := by
  have hbc : HasBlackCowCoefficient hN (by omega) (canonicalCloner (d := d) hNM.le)
      (canonicalCoefficient d N M) := by
    rw [g66m2_coef d N M hNM]; exact g68o_bc_all hd hN M hNM.le
  refine ⟨hbc, fun phi hphi => ?_⟩
  rw [hbc _ (g68o_coh_bose phi), g68o_coh_oneSite hN phi hphi, g68o_coh_trace phi hphi]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, g68o_rho_idem phi hphi, g68o_rho_trace phi hphi]
  unfold oneMixed
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, g68o_rho_trace phi hphi]
  simp only [smul_eq_mul, mul_one]
  have : ((d : ℂ))⁻¹ = (((d : ℝ))⁻¹ : ℝ) := by push_cast; rfl
  rw [this]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  ring
