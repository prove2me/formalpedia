-- Prove2me | solution 1 for UpperTheory.hermitian_diagonalisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:05:32.112591+00:00
-- url     : https://prove2.me/submissions/cc9397d8-8ada-44ce-a541-59dfc8b51aa1

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HermitianDiagonalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix in
private theorem Dz.of_submatrix {E ι κ : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {T : Matrix κ κ E}
    (h : Dz (T.submatrix e e)) : Dz T := by
  obtain ⟨g, hg, D, hD⟩ := h
  refine ⟨g.submatrix e.symm e.symm, ?_, D ∘ e.symm, ?_⟩
  · rw [det_submatrix_equiv_self]; exact hg
  · have h1 : (g.submatrix e.symm e.symm)ᴴ * T * g.submatrix e.symm e.symm
        = (gᴴ * T.submatrix e e * g).submatrix e.symm e.symm := by
      rw [← submatrix_mul_equiv _ _ _ e.symm _, ← submatrix_mul_equiv _ _ _ e.symm _]
      simp [conjTranspose_submatrix]
    rw [h1, hD]
    ext a b
    simp [diagonal_apply]
open Matrix in
private theorem Dz.of_congr {E ι : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    {T P : Matrix ι ι E} (hP : P.det ≠ 0) (h : Dz (Pᴴ * T * P)) : Dz T := by
  obtain ⟨g, hg, D, hD⟩ := h
  refine ⟨P * g, ?_, D, ?_⟩
  · rw [det_mul]; exact mul_ne_zero hP hg
  · rw [← hD, conjTranspose_mul]; simp only [Matrix.mul_assoc]
open Matrix in
private theorem Dz.sum {E A B : Type} [Field E] [StarRing E] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (hA : ∀ X : Matrix A A E, X.IsHermitian → Dz X)
    (hB : ∀ X : Matrix B B E, X.IsHermitian → Dz X)
    (T : Matrix (A ⊕ B) (A ⊕ B) E) (hT : T.IsHermitian) (hdet : T.toBlocks₁₁.det ≠ 0) :
    Dz T := by
  obtain ⟨X, Y, Z, W, rfl⟩ : ∃ X Y Z W, T = fromBlocks X Y Z W :=
    ⟨_, _, _, _, (fromBlocks_toBlocks T).symm⟩
  rw [toBlocks_fromBlocks₁₁] at hdet
  obtain ⟨h1, h2, h3, h4⟩ := (isHermitian_fromBlocks_iff).1 hT
  have hu : IsUnit X.det := isUnit_iff_ne_zero.2 hdet
  have hXX : X * X⁻¹ = 1 := mul_nonsing_inv X hu
  have hXi : X⁻¹ᴴ = X⁻¹ := by rw [conjTranspose_nonsing_inv, h1.eq]
  have hZ : Yᴴ = Z := h2
  subst hZ
  set U : Matrix (A ⊕ B) (A ⊕ B) E := fromBlocks 1 (-(X⁻¹ * Y)) 0 1 with hU
  have hUdet : U.det ≠ 0 := by
    rw [hU, det_fromBlocks_zero₂₁]; simp
  set S : Matrix B B E := W - Yᴴ * X⁻¹ * Y with hS
  have hSH : S.IsHermitian := by
    rw [IsHermitian, hS, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, hXi, h4.eq, Matrix.mul_assoc]
  have key : Uᴴ * fromBlocks X Y Yᴴ W * U = fromBlocks X 0 0 S := by
    rw [hU, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [conjTranspose_one, conjTranspose_zero, conjTranspose_neg, conjTranspose_mul, hXi,
      h1.eq]
    have hXX' : X⁻¹ * X = 1 := nonsing_inv_mul X hu
    congr 1
    · simp
    · have hY : X * (X⁻¹ * Y) = Y := by rw [← Matrix.mul_assoc, hXX, Matrix.one_mul]
      simp [hY]
    · simp [Matrix.mul_assoc, hXX']
    · simp [Matrix.mul_assoc, hXX, hXX', hS, Matrix.add_mul, Matrix.mul_add]
      abel
  refine Dz.of_congr hUdet ?_
  rw [key]
  obtain ⟨gA, hgA, DA, hDA⟩ := hA X h1
  obtain ⟨gB, hgB, DB, hDB⟩ := hB S hSH
  refine ⟨fromBlocks gA 0 0 gB, ?_, Sum.elim DA DB, ?_⟩
  · rw [det_fromBlocks_zero₂₁]; exact mul_ne_zero hgA hgB
  · rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_diagonal]
    simp [hDA, hDB]
open Matrix in
private theorem Dz.pivot {E ι : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    (ih : ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ < Fintype.card ι →
      ∀ X : Matrix κ κ E, X.IsHermitian → Dz X)
    (T : Matrix ι ι E) (hT : T.IsHermitian) (i : ι) (hi : T i i ≠ 0) : Dz T := by
  let e : {a // a = i} ⊕ {a // ¬ a = i} ≃ ι := Equiv.sumCompl _
  refine Dz.of_submatrix e ?_
  refine Dz.sum ?_ (ih _ ?_) _ (hT.submatrix e) ?_
  · intro X _
    refine ⟨1, by simp, fun a => X a a, ?_⟩
    ext a b
    have : a = b := Subsingleton.elim _ _
    subst this
    simp
  · exact Fintype.card_subtype_lt (x := i) (by simp)
  · have : Unique {a // a = i} := ⟨⟨⟨i, rfl⟩⟩, fun a => Subtype.ext a.2⟩
    rw [det_unique]
    have hdef : (((default : {a // a = i})) : ι) = i := (default : {a // a = i}).2
    simpa [e, toBlocks₁₁, hdef] using hi
open Matrix in
private theorem Dz.all {E : Type} [Field E] [StarRing E] [CharZero E] :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
      ∀ T : Matrix ι ι E, T.IsHermitian → Dz T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ _ hcard T hT
  have ih : ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ < Fintype.card ι →
      ∀ X : Matrix κ κ E, X.IsHermitian → Dz X :=
    fun κ _ _ h X hX => IH _ (hcard ▸ h) κ rfl X hX
  by_cases hd : ∃ i, T i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    exact Dz.pivot ih T hT i hi
  push_neg at hd
  by_cases h0 : T = 0
  · subst h0
    exact ⟨1, by simp, 0, by simp⟩
  obtain ⟨i, j, hij⟩ : ∃ i j, T i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (by ext a b; simpa using hc a b)
  have hne : j ≠ i := by
    rintro rfl
    exact hij (hd _)
  set c := (T i j)⁻¹ with hc
  set P : Matrix ι ι E := 1 + single j i c with hP
  have hPdet : P.det ≠ 0 := by
    have : P = transvection j i c := rfl
    rw [this, det_transvection_of_ne _ _ hne]
    exact one_ne_zero
  have hji : T j i = star (T i j) := (hT.apply j i).symm
  have hval : (Pᴴ * T * P) i i = 2 := by
    have hPH : Pᴴ = 1 + single i j (star c) := by
      rw [hP, conjTranspose_add, conjTranspose_one, conjTranspose_single]
    rw [hPH, hP]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.add_apply,
      Matrix.mul_assoc, single_mul_apply_same, mul_single_apply_same]
    have h1 : T i j * c = 1 := mul_inv_cancel₀ hij
    have h2 : star c * T j i = 1 := by
      rw [hji, ← star_mul', mul_comm, h1, star_one]
    rw [h1, h2, hd i, hd j]
    norm_num
  refine Dz.of_congr hPdet (Dz.pivot ?_ _ ?_ i ?_)
  · exact ih
  · exact isHermitian_conjTranspose_mul_mul P hT
  · rw [hval]; exact two_ne_zero
end

set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), (∀ i j, σ (T j i) = T i j) → T.det ≠ 0 → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), Matrix.transpose ((g : Matrix (Fin n) (Fin n) E).map σ) * T * (g : Matrix (Fin n) (Fin n) E) = Matrix.diagonal fun i => algebraMap F E (D i : F) := by
  intro F E _ _ _ _ σ hσ hfix n T hT hdet
  letI : StarRing E :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by
        show σ (a * b) = σ b * σ a
        rw [map_mul, mul_comm]
      star_add := map_add σ }
  have hstar : ∀ x : E, star x = σ x := fun _ => rfl
  have hH : T.IsHermitian := by
    ext i j
    exact hT i j
  obtain ⟨g, hg, D, hD⟩ := Dz.all n (Fin n) (by simp) T hH
  have hct : Matrix.transpose (g.map σ) = Matrix.conjTranspose g := rfl
  have hDH : (Matrix.diagonal D).IsHermitian := by
    rw [← hD]
    have := Matrix.isHermitian_conjTranspose_mul_mul g hH
    exact this
  have hfixD : ∀ i, σ (D i) = D i := by
    intro i
    have := hDH.apply i i
    simpa [hstar] using this
  have hdD : ∀ i, D i ≠ 0 := by
    intro i h0
    have h1 : (Matrix.diagonal D).det = 0 := by
      rw [Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [← hD, Matrix.det_mul, Matrix.det_mul] at h1
    have h2 : (Matrix.conjTranspose g).det ≠ 0 := by
      rw [Matrix.det_conjTranspose]
      intro h3
      exact hg (by simpa using h3)
    exact mul_ne_zero (mul_ne_zero h2 hdet) hg h1
  choose d hd using fun i => hfix (D i) (hfixD i)
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h0
    apply hdD i
    rw [← hd, h0, map_zero]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hg, fun i => Units.mk0 (d i) (hd0 i), ?_⟩
  have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero g hg : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) = g := rfl
  rw [hcoe, hct, hD]
  congr 1
  ext i
  simp [hd]
end UpperTheory
