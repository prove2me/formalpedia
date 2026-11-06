-- Prove2me | solution 1 for StrongConv.prob_norm_eval_sModel_ge_le_without_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:54:21.605206+00:00
-- url     : https://prove2.me/submissions/d0835be2-3036-47bc-a0d7-29674d1990bd

import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_prob_norm_eval_sModel_ge_le
import Mathlib

section
section
open scoped InnerProductSpace
open Matrix

noncomputable section

namespace StrongConv.W2Sec3


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tensorOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (y : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    tensorOp A T y a = ∑ b, A a b • T (y b) := by
  unfold tensorOp
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.single_apply,
    PiLp.proj_apply, PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_sum, WithLp.ofLp_smul,
    WithLp.ofLp_toLp, Pi.smul_apply, Pi.single_apply]
  simp [Finset.sum_comm (γ := Fin n)]

lemma inner_tensorOp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin m => H)) (y : PiLp 2 (fun _ : Fin n => H)) :
    ⟪x, tensorOp A T y⟫_ℂ = ∑ a, ∑ b, A a b * ⟪x a, T (y b)⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tensorOp_apply, inner_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [inner_smul_right]

lemma star_tensorOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    star (tensorOp A T) = tensorOp Aᴴ (star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  -- ⟪tensorOp Aᴴ T† x, y⟫ = ⟪x, tensorOp A T y⟫
  rw [inner_tensorOp, ← inner_conj_symm, inner_tensorOp, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, inner_conj_symm]
  simp only [Matrix.conjTranspose_apply, star_star, Complex.star_def]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  simp only [Complex.conj_conj]

lemma star_letterOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (l : Fin d ⊕ Fin d) :
    star (letterOp u l) = letterOp u l.swap := by
  rcases l with i | i <;> simp [letterOp]

lemma star_list_prod' {A : Type*} [Monoid A] [StarMul A] (l : List A) :
    star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, star_mul]

lemma star_wordOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    star (wordOp u w) = wordOp u (NCPoly.wordStar w) := by
  unfold wordOp NCPoly.wordStar
  rw [star_list_prod']
  simp only [FreeMonoid.toList_ofList, List.map_map, List.map_reverse]
  congr 1
  congr 1
  apply List.map_congr_left
  intro l _
  simp [star_letterOp]

lemma wordStar_wordStar {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) :
    NCPoly.wordStar (NCPoly.wordStar w) = w := by
  unfold NCPoly.wordStar
  apply FreeMonoid.toList.injective
  simp [Function.comp_def]


end StrongConv.W2Sec3

end
end
end

section
section
open scoped InnerProductSpace
open Matrix

noncomputable section

namespace StrongConv
namespace W2Sec3

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- block matrix `[[0, A], [B, 0]]` -/
def blk {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin (D + D)) (Fin (D + D)) ℂ :=
  Matrix.of fun i j => Fin.addCases (fun a => Fin.addCases (fun _ => 0) (fun b => A a b) j)
    (fun a => Fin.addCases (fun b => B a b) (fun _ => 0) j) i

@[simp] lemma blk_cc {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) (a b : Fin D) :
    blk A B (Fin.castAdd D a) (Fin.castAdd D b) = 0 := by simp only [blk, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
@[simp] lemma blk_cn {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) (a b : Fin D) :
    blk A B (Fin.castAdd D a) (Fin.natAdd D b) = A a b := by simp only [blk, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
@[simp] lemma blk_nc {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) (a b : Fin D) :
    blk A B (Fin.natAdd D a) (Fin.castAdd D b) = B a b := by simp only [blk, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
@[simp] lemma blk_nn {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) (a b : Fin D) :
    blk A B (Fin.natAdd D a) (Fin.natAdd D b) = 0 := by simp only [blk, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]

lemma blk_zero {D : ℕ} : blk (0 : Matrix (Fin D) (Fin D) ℂ) 0 = 0 := by
  ext i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;> simp only [blk_cc, blk_cn, blk_nc, blk_nn, Matrix.zero_apply]

lemma blk_conjTranspose {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) :
    (blk A B)ᴴ = blk Bᴴ Aᴴ := by
  ext i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;> simp only [Matrix.conjTranspose_apply, blk_cc, blk_cn, blk_nc, blk_nn, star_zero]

/-- the Hermitian dilation `[[0, P], [P*, 0]]` -/
def dil {D d : ℕ} (P : NCPoly D d) : NCPoly (D + D) d :=
  Finsupp.ofSupportFinite (fun w => blk (P w) (P (NCPoly.wordStar w))ᴴ) (by
    classical
    apply (((P.support ∪ P.support.image NCPoly.wordStar) : Finset _).finite_toSet).subset
    intro w hw
    simp only [Function.mem_support, ne_eq] at hw
    by_contra h
    apply hw
    have h1 : P w = 0 := by
      by_contra hne
      exact h (by simp [Finsupp.mem_support_iff, hne])
    have h2 : P (NCPoly.wordStar w) = 0 := by
      by_contra hne
      exact h (by
        simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Finset.mem_coe,
          Finsupp.mem_support_iff, Set.mem_image]
        exact Or.inr ⟨_, hne, wordStar_wordStar w⟩)
    rw [h1, h2]; simpa using blk_zero)

lemma dil_apply {D d : ℕ} (P : NCPoly D d) (w) :
    dil P w = blk (P w) (P (NCPoly.wordStar w))ᴴ := rfl

lemma dil_isSelfAdjoint {D d : ℕ} (P : NCPoly D d) : (dil P).IsSelfAdjoint := by
  intro w
  rw [dil_apply, dil_apply, blk_conjTranspose, wordStar_wordStar]
  simp

lemma dil_degree {D d : ℕ} (P : NCPoly D d) : (dil P).degree ≤ P.degree := by
  unfold NCPoly.degree
  apply Finset.sup_le
  intro w hw
  rw [Finsupp.mem_support_iff, dil_apply] at hw
  by_cases h : P w = 0
  · have h2 : P (NCPoly.wordStar w) ≠ 0 := by
      intro h2; apply hw; rw [h, h2]; simpa using blk_zero
    have := Finset.le_sup (f := FreeMonoid.length) (Finsupp.mem_support_iff.mpr h2)
    have hl : (NCPoly.wordStar w).length = w.length := by
      simp [NCPoly.wordStar, FreeMonoid.length]
    rw [hl] at this; exact this
  · exact Finset.le_sup (f := FreeMonoid.length) (Finsupp.mem_support_iff.mpr h)


open Classical in
lemma eval_dil_apply {D d : ℕ} (P : NCPoly D d) (u : Fin d → H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin (D + D) => H)) (i : Fin (D + D)) :
    (dil P).eval u x i = ∑ w ∈ P.support ∪ P.support.image NCPoly.wordStar,
      ∑ j, dil P w i j • wordOp u w (x j) := by
  unfold NCPoly.eval
  rw [ContinuousLinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  have hsub : (dil P).support ⊆ P.support ∪ P.support.image NCPoly.wordStar := by
    intro w hw
    rw [Finsupp.mem_support_iff, dil_apply] at hw
    by_contra h
    apply hw
    have h1 : P w = 0 := by
      by_contra hne
      exact h (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hne))
    have h2 : P (NCPoly.wordStar w) = 0 := by
      by_contra hne
      exact h (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, Finsupp.mem_support_iff.mpr hne,
        wordStar_wordStar w⟩))
    rw [h1, h2]; simpa using blk_zero
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [tensorOp_apply]
  · intro w _ hw
    rw [Finsupp.notMem_support_iff.mp hw]
    simp [tensorOp_apply]


def lo {D : ℕ} (x : PiLp 2 (fun _ : Fin (D + D) => H)) : PiLp 2 (fun _ : Fin D => H) :=
  WithLp.toLp 2 (fun b => x (Fin.castAdd D b))

def hi {D : ℕ} (x : PiLp 2 (fun _ : Fin (D + D) => H)) : PiLp 2 (fun _ : Fin D => H) :=
  WithLp.toLp 2 (fun b => x (Fin.natAdd D b))

lemma eval_apply' {D d : ℕ} (P : NCPoly D d) (u : Fin d → H →L[ℂ] H)
    (y : PiLp 2 (fun _ : Fin D => H)) (a : Fin D) :
    P.eval u y a = ∑ w ∈ P.support, ∑ b, P w a b • wordOp u w (y b) := by
  unfold NCPoly.eval
  rw [ContinuousLinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [tensorOp_apply]

open Classical in
lemma dil_upper {D d : ℕ} (P : NCPoly D d) (u : Fin d → H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin (D + D) => H)) (a : Fin D) :
    (dil P).eval u x (Fin.castAdd D a) = P.eval u (hi x) a := by
  rw [eval_dil_apply, eval_apply']
  have : ∀ w ∈ P.support ∪ P.support.image NCPoly.wordStar,
      ∑ j, dil P w (Fin.castAdd D a) j • wordOp u w (x j) =
        ∑ b, P w a b • wordOp u w (x (Fin.natAdd D b)) := by
    intro w _
    rw [Fin.sum_univ_add]
    simp only [dil_apply, blk_cc, blk_cn, zero_smul, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_congr rfl this]
  symm
  apply Finset.sum_subset Finset.subset_union_left
  intro w _ hw
  rw [Finsupp.notMem_support_iff.mp hw]
  simp

open Classical in
lemma dil_lower {D d : ℕ} (P : NCPoly D d) (u : Fin d → H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin (D + D) => H)) (a : Fin D) :
    (dil P).eval u x (Fin.natAdd D a) = (star (P.eval u)) (lo x) a := by
  have hs : star (P.eval u) = ∑ w ∈ P.support, tensorOp (P w)ᴴ (wordOp u (NCPoly.wordStar w)) := by
    unfold NCPoly.eval
    have hs : star (∑ w ∈ P.support, tensorOp (P w) (wordOp u w)) =
        ∑ w ∈ P.support, star (tensorOp (P w) (wordOp u w)) := by
      simp only [ContinuousLinearMap.star_eq_adjoint]
      exact map_sum ContinuousLinearMap.adjoint _ _
    rw [hs]
    simp only [star_tensorOp, star_wordOp]
  rw [hs, eval_dil_apply, ContinuousLinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  have h1 : ∀ w ∈ P.support ∪ P.support.image NCPoly.wordStar,
      ∑ j, dil P w (Fin.natAdd D a) j • wordOp u w (x j) =
        ∑ b, (P (NCPoly.wordStar w))ᴴ a b • wordOp u w (lo x b) := by
    intro w _
    rw [Fin.sum_univ_add]
    simp only [dil_apply, blk_nc, blk_nn, zero_smul, Finset.sum_const_zero, add_zero, lo,
      WithLp.ofLp_toLp]
  rw [Finset.sum_congr rfl h1]
  have h2 : ∑ w ∈ P.support ∪ P.support.image NCPoly.wordStar,
      ∑ b, (P (NCPoly.wordStar w))ᴴ a b • wordOp u w (lo x b) =
      ∑ w ∈ P.support.image NCPoly.wordStar,
      ∑ b, (P (NCPoly.wordStar w))ᴴ a b • wordOp u w (lo x b) := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro w _ hw
    have : P (NCPoly.wordStar w) = 0 := by
      by_contra hne
      exact hw (Finset.mem_image.mpr ⟨_, Finsupp.mem_support_iff.mpr hne, wordStar_wordStar w⟩)
    simp [this]
  rw [h2, Finset.sum_image (fun v _ w _ h => by
    have := congrArg NCPoly.wordStar h
    rwa [wordStar_wordStar, wordStar_wordStar] at this)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [tensorOp_apply, wordStar_wordStar]


lemma norm_sq_split {D : ℕ} (x : PiLp 2 (fun _ : Fin (D + D) => H)) :
    ‖x‖ ^ 2 = ‖lo x‖ ^ 2 + ‖hi x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_add]
  rfl

lemma norm_eval_dil {D d : ℕ} (P : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    ‖(dil P).eval u‖ = ‖P.eval u‖ := by
  set E := P.eval u with hE
  set Z := (dil P).eval u with hZ
  have hlo : ∀ x, lo (Z x) = E (hi x) := fun x => by
    ext a; exact dil_upper P u x a
  have hhi : ∀ x, hi (Z x) = (star E) (lo x) := fun x => by
    ext a; exact dil_lower P u x a
  have key : ∀ x, ‖Z x‖ ^ 2 = ‖E (hi x)‖ ^ 2 + ‖(star E) (lo x)‖ ^ 2 := fun x => by
    rw [norm_sq_split, hlo, hhi]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, key, mul_pow,
      norm_sq_split]
    have h1 : ‖E (hi x)‖ ^ 2 ≤ ‖E‖ ^ 2 * ‖hi x‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (E.le_opNorm _) 2
    have h2 : ‖(star E) (lo x)‖ ^ 2 ≤ ‖E‖ ^ 2 * ‖lo x‖ ^ 2 := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      calc ‖(star E) (lo x)‖ ≤ ‖star E‖ * ‖lo x‖ := (star E).le_opNorm _
        _ = ‖E‖ * ‖lo x‖ := by rw [_root_.norm_star E]
    nlinarith
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    let x : PiLp 2 (fun _ : Fin (D + D) => H) :=
      WithLp.toLp 2 (Fin.append (fun _ : Fin D => (0 : H)) y.ofLp)
    have hx : hi x = y := by
      ext a; simp only [hi, x, WithLp.ofLp_toLp, Fin.append_right]
    have hx0 : lo x = 0 := by
      ext a; simp only [lo, x, WithLp.ofLp_toLp, Fin.append_left]; rfl
    have h1 := key x
    rw [hx, hx0] at h1
    have h2 : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by rw [norm_sq_split, hx, hx0]; simp
    have h3 : ‖E y‖ ≤ ‖Z‖ * ‖x‖ := by
      have : ‖Z x‖ = ‖E y‖ := by
        have := h1; simp only [map_zero, norm_zero] at this
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa using h1)
      rw [← this]; exact Z.le_opNorm x
    have h5 : ‖x‖ = ‖y‖ := by
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
    rwa [h5] at h3


lemma fullNorm_dil {D d : ℕ} (P : NCPoly D d) : (dil P).fullNorm = P.fullNorm := by
  unfold NCPoly.fullNorm
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, norm_eval_dil]

end W2Sec3

theorem prob_norm_eval_sModel_ge_le_without_selfAdjoint_dev :
    ∃ C : ℝ, ∀ D d q₀ : ℕ, 2 ≤ d → ∀ P : NCPoly D d, P.degree ≤ q₀ →
      ∀ ε : ℝ, 0 < ε → ε < P.fullNorm - ‖P.eval (sLimit d)‖ → ∀ N : ℕ,
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ‖P.eval (sLimit d)‖ + ε ≤ ‖P.eval (sModel σ)‖) ≤
        C * (D / N) * (P.fullNorm * q₀ * Real.log d / ε) ^ 8 *
          Real.log (Real.exp 1 * P.fullNorm / ε) := by
  obtain ⟨C, hC⟩ := prob_norm_eval_sModel_ge_le
  refine ⟨2 * C, fun D d q₀ hd P hdeg ε hε hε2 N => ?_⟩
  have h := hC (D + D) d q₀ hd (W2Sec3.dil P) (W2Sec3.dil_isSelfAdjoint P)
    (le_trans (W2Sec3.dil_degree P) hdeg) ε hε
    (by rw [W2Sec3.fullNorm_dil, W2Sec3.norm_eval_dil]; exact hε2) N
  simp only [W2Sec3.fullNorm_dil, W2Sec3.norm_eval_dil] at h
  refine h.trans_eq ?_
  push_cast
  ring

end StrongConv

end
end
end

section
open StrongConv

theorem solution :
    ∃ C : ℝ, ∀ D d q₀ : ℕ, 2 ≤ d → ∀ P : NCPoly D d, P.degree ≤ q₀ →
      ∀ ε : ℝ, 0 < ε → ε < P.fullNorm - ‖P.eval (sLimit d)‖ → ∀ N : ℕ,
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ‖P.eval (sLimit d)‖ + ε ≤ ‖P.eval (sModel σ)‖) ≤
        C * (D / N) * (P.fullNorm * q₀ * Real.log d / ε) ^ 8 *
          Real.log (Real.exp 1 * P.fullNorm / ε) := by
  apply StrongConv.prob_norm_eval_sModel_ge_le_without_selfAdjoint_dev <;> assumption

end
