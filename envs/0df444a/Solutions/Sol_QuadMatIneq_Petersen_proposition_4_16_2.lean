-- Prove2me | solution 2 for QuadMatIneq.Petersen.proposition_4_16
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T06:02:19.696752+00:00
-- url     : https://prove2.me/submissions/2aa3327b-f2e4-44f5-a59e-719761c3c827

import Mathlib
import Definitions.Def_QuadMatIneq_Petersen_QMI
import Definitions.Def_QuadMatIneq_Petersen_Setup
import Theorems.Thm_Matrix_sLemma_strict

-- carved verbatim out of submission 3f9c8340-4ab7-435c-a3bc-21b936114f72, lines 1738-1757

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]

def MA (C : Matrix a a ℝ) (E : Matrix a b ℝ) : Matrix (a ⊕ b) (a ⊕ b) ℝ :=
  fromBlocks (-C) (-E) (-E)ᵀ 0

end

section
open Matrix

lemma isSymm_blocks {a b : Type*} (P : Matrix a a ℝ) (Q : Matrix a b ℝ) (R : Matrix b b ℝ)
    (hP : Pᵀ = P) (hR : Rᵀ = R) : (fromBlocks P Q Qᵀ R).IsSymm := by
  unfold Matrix.IsSymm
  rw [fromBlocks_transpose, hP, hR, transpose_transpose]

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

lemma transpose_of_herm {M : Matrix a a ℝ} (h : M.IsHermitian) : Mᵀ = M := by
  have := h.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]

omit [DecidableEq b] in
lemma MA_symm (C : Matrix a a ℝ) (E : Matrix a b ℝ) (hC : C.IsHermitian) : (MA C E).IsSymm :=
  isSymm_blocks _ _ _ (by rw [transpose_neg, transpose_of_herm hC]) (by simp)

def MB (Fbar : Matrix c c ℝ) (G : Matrix c a ℝ) : Matrix (a ⊕ b) (a ⊕ b) ℝ :=
  fromBlocks (Gᵀ * Fbar * G) 0 (0 : Matrix a b ℝ)ᵀ (-1)

lemma MB_symm (Fbar : Matrix c c ℝ) (G : Matrix c a ℝ) (hF : Fbar.IsHermitian) :
    (MB (b := b) Fbar G).IsSymm :=
  isSymm_blocks _ _ _ (by rw [transpose_mul, transpose_mul, transpose_transpose,
    transpose_of_herm hF, Matrix.mul_assoc]) (by simp)

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private lemma aux2_pair_real (ax bx ay by' ka kb s₁ s₂ : ℝ) (hx : 0 < bx) (hs₁ : s₁ < 0) (hs₂ : 0 < s₂)
    (hb₁ : bx + s₁ * kb + s₁ ^ 2 * by' = 0) (hb₂ : bx + s₂ * kb + s₂ ^ 2 * by' = 0)
    (ha₁ : 0 ≤ ax + s₁ * ka + s₁ ^ 2 * ay) (ha₂ : 0 ≤ ax + s₂ * ka + s₂ ^ 2 * ay) :
    0 ≤ ay * bx - ax * by' := by
  by_contra hC
  push Not at hC
  set C := ay * bx - ax * by'
  set γ := ka * bx - ax * kb
  -- h(s) = (a-part)·bx - ax·(b-part) = s γ + s² C
  have e₁ : (ax + s₁ * ka + s₁ ^ 2 * ay) * bx - ax * (bx + s₁ * kb + s₁ ^ 2 * by') =
      s₁ * (γ + s₁ * C) := by simp only [γ, C]; ring
  have e₂ : (ax + s₂ * ka + s₂ ^ 2 * ay) * bx - ax * (bx + s₂ * kb + s₂ ^ 2 * by') =
      s₂ * (γ + s₂ * C) := by simp only [γ, C]; ring
  rw [hb₁, mul_zero, sub_zero] at e₁
  rw [hb₂, mul_zero, sub_zero] at e₂
  have h₁ : 0 ≤ s₁ * (γ + s₁ * C) := e₁ ▸ mul_nonneg ha₁ hx.le
  have h₂ : 0 ≤ s₂ * (γ + s₂ * C) := e₂ ▸ mul_nonneg ha₂ hx.le
  have h₁' : γ + s₁ * C ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  have h₂' : 0 ≤ γ + s₂ * C := by
    by_contra h; push Not at h; nlinarith
  nlinarith

private lemma aux2_roots (bx by' kb : ℝ) (hx : 0 < bx) (hy : by' < 0) :
    ∃ s₁ s₂ : ℝ, s₁ < 0 ∧ 0 < s₂ ∧ bx + s₁ * kb + s₁ ^ 2 * by' = 0 ∧
      bx + s₂ * kb + s₂ ^ 2 * by' = 0 := by
  have hD : 0 ≤ kb ^ 2 - 4 * bx * by' := by nlinarith
  set r := Real.sqrt (kb ^ 2 - 4 * bx * by') with hr_def
  have hr2 : r ^ 2 = kb ^ 2 - 4 * bx * by' := Real.sq_sqrt hD
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrk1 : kb < r := by nlinarith
  have hrk2 : -kb < r := by nlinarith
  have hy2 : (2 * by') ≠ 0 := by linarith
  have hy4 : (4 * by') ≠ 0 := by linarith
  refine ⟨(-kb + r) / (2 * by'), (-kb - r) / (2 * by'), ?_, ?_, ?_, ?_⟩
  · exact div_neg_of_pos_of_neg (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · set s := (-kb + r) / (2 * by')
    have hs : 2 * by' * s = -kb + r := by simp only [s]; field_simp; exact mul_div_cancel_left₀ _ (ne_of_lt hy)
    have : 4 * by' * (bx + s * kb + s ^ 2 * by') = 0 := by
      linear_combination (2 * by' * s + kb + r) * hs + hr2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hy4
    · exact h
  · set s := (-kb - r) / (2 * by')
    have hs : 2 * by' * s = -kb - r := by simp only [s]; field_simp; exact mul_div_cancel_left₀ _ (ne_of_lt hy)
    have : 4 * by' * (bx + s * kb + s ^ 2 * by') = 0 := by
      linear_combination (2 * by' * s + kb - r) * hs + hr2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hy4
    · exact h

private lemma aux2_core {V : Type*} [AddCommGroup V] [Module ℝ V] (a b : V → ℝ)
    (ha : ∀ x y : V, ∃ k : ℝ, ∀ s : ℝ, a (x + s • y) = a x + s * k + s ^ 2 * a y)
    (hb : ∀ x y : V, ∃ k : ℝ, ∀ s : ℝ, b (x + s • y) = b x + s * k + s ^ 2 * b y)
    (hslater : ∃ x₀, 0 < b x₀) (H : ∀ x, 0 ≤ b x → 0 ≤ a x) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∀ x, 0 ≤ a x - τ * b x := by
  -- pair inequality
  have hpair : ∀ x y, 0 < b x → b y < 0 → 0 ≤ a y * b x - a x * b y := by
    intro x y hx hy
    obtain ⟨ka, hka⟩ := ha x y
    obtain ⟨kb, hkb⟩ := hb x y
    obtain ⟨s₁, s₂, hs₁, hs₂, h₁, h₂⟩ := aux2_roots (b x) (b y) kb hx hy
    refine aux2_pair_real (a x) (b x) (a y) (b y) ka kb s₁ s₂ hx hs₁ hs₂ h₁ h₂ ?_ ?_
    · rw [← hka]; exact H _ (by rw [hkb, h₁])
    · rw [← hka]; exact H _ (by rw [hkb, h₂])
  obtain ⟨x₀, hx₀⟩ := hslater
  let S : Set ℝ := {q | ∃ x, 0 < b x ∧ q = a x / b x}
  have hSne : S.Nonempty := ⟨_, x₀, hx₀, rfl⟩
  have hS0 : ∀ q ∈ S, 0 ≤ q := by
    rintro q ⟨x, hx, rfl⟩; exact div_nonneg (H x hx.le) hx.le
  have hSbdd : BddBelow S := ⟨0, hS0⟩
  refine ⟨sInf S, le_csInf hSne hS0, fun x => ?_⟩
  rcases lt_trichotomy (b x) 0 with hneg | hzero | hpos
  · have hle : a x / b x ≤ sInf S := by
      refine le_csInf hSne ?_
      rintro q ⟨z, hz, rfl⟩
      rw [div_le_iff_of_neg hneg, div_mul_eq_mul_div, div_le_iff₀ hz]
      linarith [hpair z x hz hneg]
    rw [div_le_iff_of_neg hneg] at hle
    linarith
  · rw [hzero, mul_zero, sub_zero]; exact H x hzero.ge
  · have hle : sInf S ≤ a x / b x := csInf_le hSbdd ⟨x, hpos, rfl⟩
    rw [le_div_iff₀ hpos] at hle
    linarith

private lemma aux2_isHermitian {n : Type*} {A : Matrix n n ℝ} (hA : A.IsSymm) : A.IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact hA

private lemma aux2_qexp {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x y : n → ℝ) (s : ℝ) :
    (x + s • y) ⬝ᵥ A *ᵥ (x + s • y) =
      x ⬝ᵥ A *ᵥ x + s * (x ⬝ᵥ A *ᵥ y + y ⬝ᵥ A *ᵥ x) + s ^ 2 * (y ⬝ᵥ A *ᵥ y) := by
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

private lemma aux2_qf_sub_smul {n : Type*} [Fintype n] (A B : Matrix n n ℝ) (τ : ℝ) (x : n → ℝ) :
    x ⬝ᵥ (A - τ • B) *ᵥ x = x ⬝ᵥ A *ᵥ x - τ * (x ⬝ᵥ B *ᵥ x) := by
  simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]

private lemma aux2_symm_sub_smul {n : Type*} {A B : Matrix n n ℝ} (hA : A.IsSymm) (hB : B.IsSymm)
    (τ : ℝ) : (A - τ • B).IsSymm := by
  unfold IsSymm at *
  rw [transpose_sub, transpose_smul, hA, hB]

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

lemma dot_mulVec_eq (E : Matrix a b ℝ) (x : a → ℝ) (w : b → ℝ) :
    x ⬝ᵥ E *ᵥ w = (Eᵀ *ᵥ x) ⬝ᵥ w := by
  rw [dotProduct_mulVec, mulVec_transpose]

lemma dot_self_nonneg (v : a → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma herm_of_transpose {M : Matrix a a ℝ} (h : Mᵀ = M) : M.IsHermitian := by
  unfold Matrix.IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact h

lemma qf_transpose_mul (F : Matrix b a ℝ) (x : a → ℝ) :
    x ⬝ᵥ (Fᵀ * F) *ᵥ x = (F *ᵥ x) ⬝ᵥ (F *ᵥ x) := by
  rw [← mulVec_mulVec, dot_mulVec_eq, transpose_transpose]

end

section
open Matrix

lemma scal_cs (t α β γ ω : ℝ) (htα : t * α = β) (hω : ω ≤ α)
    (h : 0 ≤ γ - 2 * t * β + t ^ 2 * α) : 0 ≤ γ - t ^ 2 * ω := by
  subst htα
  nlinarith [mul_le_mul_of_nonneg_left hω (sq_nonneg t)]

lemma vecMulVec_mulVec' {p q : Type*} [Fintype q] (w : p → ℝ) (v u : q → ℝ) :
    vecMulVec w v *ᵥ u = (v ⬝ᵥ u) • w := by
  ext i; simp [mulVec, dotProduct, vecMulVec, mul_assoc]
  rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun j _ => by ring)

lemma exists_F {p q : Type*} [Fintype p] [Fintype q] (Fbar : Matrix q q ℝ)
    (hF : Fbar.PosSemidef) (u : q → ℝ) (w : p → ℝ) (h : w ⬝ᵥ w ≤ u ⬝ᵥ Fbar *ᵥ u) :
    ∃ F : Matrix p q ℝ, (Fbar - Fᵀ * F).PosSemidef ∧ F *ᵥ u = w := by
  have hsym : Fbarᵀ = Fbar := transpose_of_herm hF.1
  have hnn : ∀ z : q → ℝ, 0 ≤ z ⬝ᵥ Fbar *ᵥ z := fun z => by
    simpa using hF.dotProduct_mulVec_nonneg z
  have hcomm : ∀ z y : q → ℝ, z ⬝ᵥ Fbar *ᵥ y = y ⬝ᵥ Fbar *ᵥ z := fun z y => by
    rw [dot_mulVec_eq, hsym, dotProduct_comm]
  set α := u ⬝ᵥ Fbar *ᵥ u with hα
  rcases (hnn u).eq_or_lt with h0 | hpos
  · have hw : w = 0 := by
      apply dotProduct_self_eq_zero.mp
      exact le_antisymm (by linarith) (dot_self_nonneg w)
    refine ⟨0, ?_, ?_⟩
    · simpa using hF
    · simp [hw]
  · refine ⟨α⁻¹ • vecMulVec w (Fbar *ᵥ u), ?_, ?_⟩
    · rw [posSemidef_iff_dotProduct_mulVec]
      refine ⟨herm_of_transpose ?_, fun z => ?_⟩
      · rw [transpose_sub, transpose_mul, transpose_transpose, hsym]
      · rw [star_trivial, sub_mulVec, dotProduct_sub, qf_transpose_mul, smul_mulVec,
          vecMulVec_mulVec', smul_smul]
        simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
        set β := (Fbar *ᵥ u) ⬝ᵥ z
        have hcs := hnn (z - (α⁻¹ * β) • u)
        rw [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub,
          smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_eq_mul,
          smul_eq_mul, smul_eq_mul] at hcs
        have e1 : z ⬝ᵥ Fbar *ᵥ u = β := by rw [dotProduct_comm]
        have e2 : u ⬝ᵥ Fbar *ᵥ z = β := by rw [hcomm, e1]
        rw [e1, e2, ← hα] at hcs
        simp only [smul_eq_mul] at hcs
        have := scal_cs (α⁻¹ * β) α β (z ⬝ᵥ Fbar *ᵥ z) (w ⬝ᵥ w)
          (by rw [mul_assoc, mul_comm β, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]) h
          (by linarith)
        linarith [this, show (α⁻¹ * β) ^ 2 * w ⬝ᵥ w = α⁻¹ * β * (α⁻¹ * β * w ⬝ᵥ w) by ring]
    · rw [smul_mulVec, vecMulVec_mulVec', smul_smul, dotProduct_comm, ← hcomm, ← hα,
        inv_mul_cancel₀ hpos.ne', one_smul]

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]

omit [DecidableEq b] in
lemma exists_F_of (Fbar : Matrix c c ℝ) (hFbar : Fbar.PosSemidef) (G : Matrix c a ℝ)
    (x : a → ℝ) (w : b → ℝ) (h : 0 ≤ (G *ᵥ x) ⬝ᵥ Fbar *ᵥ (G *ᵥ x) - w ⬝ᵥ w) :
    ∃ F ∈ (QuadMatIneq.Petersen.uncSet Fbar : Set (Matrix b c ℝ)), F *ᵥ (G *ᵥ x) = w := by
  obtain ⟨F, hF, hFu⟩ := exists_F Fbar hFbar (G *ᵥ x) w (by linarith)
  exact ⟨F, hF, hFu⟩

omit [DecidableEq b] in
lemma herm_target (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ)
    (G : Matrix c a ℝ) (lam : ℝ) (hC : C.IsHermitian) (hF : Fbar.IsHermitian) :
    (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).IsHermitian := by
  apply herm_of_transpose
  rw [transpose_neg, transpose_add, transpose_add, transpose_smul, transpose_smul,
    transpose_mul, transpose_mul, transpose_mul, transpose_transpose, transpose_transpose,
    transpose_of_herm hC, transpose_of_herm hF, Matrix.mul_assoc]

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

lemma qf_blocks (P : Matrix a a ℝ) (Q : Matrix a b ℝ) (R : Matrix b b ℝ) (x : a → ℝ)
    (w : b → ℝ) :
    Sum.elim x w ⬝ᵥ fromBlocks P Q Qᵀ R *ᵥ Sum.elim x w =
      x ⬝ᵥ P *ᵥ x + 2 * ((Qᵀ *ᵥ x) ⬝ᵥ w) + w ⬝ᵥ R *ᵥ w := by
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim, dotProduct_add]
  rw [dot_mulVec_eq Q x w, dotProduct_comm w (Qᵀ *ᵥ x)]
  ring

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]

omit [DecidableEq b] in
lemma qA (C : Matrix a a ℝ) (E : Matrix a b ℝ) (x : a → ℝ) (w : b → ℝ) :
    Sum.elim x w ⬝ᵥ MA C E *ᵥ Sum.elim x w = -(x ⬝ᵥ C *ᵥ x) - 2 * ((Eᵀ *ᵥ x) ⬝ᵥ w) := by
  rw [MA, qf_blocks]
  simp only [neg_mulVec, dotProduct_neg, transpose_neg, zero_mulVec, dotProduct_zero, add_zero,
    neg_dotProduct]
  ring

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

lemma qf_conj (F : Matrix b b ℝ) (G : Matrix b a ℝ) (x : a → ℝ) :
    x ⬝ᵥ (Gᵀ * F * G) *ᵥ x = (G *ᵥ x) ⬝ᵥ F *ᵥ (G *ᵥ x) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dot_mulVec_eq, transpose_transpose]

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]

lemma qB (Fbar : Matrix c c ℝ) (G : Matrix c a ℝ) (x : a → ℝ) (w : b → ℝ) :
    Sum.elim x w ⬝ᵥ MB Fbar G *ᵥ Sum.elim x w = (G *ᵥ x) ⬝ᵥ Fbar *ᵥ (G *ᵥ x) - w ⬝ᵥ w := by
  rw [MB, qf_blocks, qf_conj]
  simp only [transpose_zero, zero_mulVec, zero_dotProduct, mul_zero, add_zero, neg_mulVec,
    one_mulVec, dotProduct_neg]
  ring

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

lemma qf_mul_transpose (E : Matrix a b ℝ) (x : a → ℝ) :
    x ⬝ᵥ (E * Eᵀ) *ᵥ x = (Eᵀ *ᵥ x) ⬝ᵥ (Eᵀ *ᵥ x) := by
  rw [← mulVec_mulVec, dot_mulVec_eq]

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]

omit [DecidableEq b] in
lemma qf_target (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ) (G : Matrix c a ℝ)
    (lam : ℝ) (x : a → ℝ) :
    x ⬝ᵥ (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))) *ᵥ x =
      -(x ⬝ᵥ C *ᵥ x) - lam * ((Eᵀ *ᵥ x) ⬝ᵥ (Eᵀ *ᵥ x)) -
        lam⁻¹ * ((G *ᵥ x) ⬝ᵥ Fbar *ᵥ (G *ᵥ x)) := by
  rw [neg_mulVec, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, dotProduct_neg,
    dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    qf_mul_transpose, qf_conj]
  ring

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

lemma qf_EFG (E : Matrix a b ℝ) (F : Matrix b c ℝ) (G : Matrix c a ℝ) (x : a → ℝ) :
    x ⬝ᵥ (E * F * G) *ᵥ x = (Eᵀ *ᵥ x) ⬝ᵥ (F *ᵥ (G *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dot_mulVec_eq]

lemma qf_transpose (M : Matrix a a ℝ) (x : a → ℝ) : x ⬝ᵥ Mᵀ *ᵥ x = x ⬝ᵥ M *ᵥ x := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]

omit [DecidableEq b] in
lemma qf_unc (C : Matrix a a ℝ) (E : Matrix a b ℝ) (F : Matrix b c ℝ) (G : Matrix c a ℝ)
    (x : a → ℝ) :
    x ⬝ᵥ (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)) *ᵥ x =
      -(x ⬝ᵥ C *ᵥ x) - 2 * ((Eᵀ *ᵥ x) ⬝ᵥ (F *ᵥ (G *ᵥ x))) := by
  have ht : Gᵀ * Fᵀ * Eᵀ = (E * F * G)ᵀ := by rw [transpose_mul, transpose_mul, Matrix.mul_assoc]
  rw [ht, neg_mulVec, add_mulVec, add_mulVec, dotProduct_neg, dotProduct_add, dotProduct_add,
    qf_transpose, qf_EFG]
  ring

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem Matrix.sLemma {n : Type*} [Fintype n] {A B : Matrix n n ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) (hslater : ∃ x₀, 0 < x₀ ⬝ᵥ B *ᵥ x₀) :
    (∀ x, 0 ≤ x ⬝ᵥ B *ᵥ x → 0 ≤ x ⬝ᵥ A *ᵥ x) ↔ ∃ τ : ℝ, 0 ≤ τ ∧ (A - τ • B).PosSemidef := by
  constructor
  · intro H
    obtain ⟨τ, hτ, h⟩ := aux2_core (fun x => x ⬝ᵥ A *ᵥ x) (fun x => x ⬝ᵥ B *ᵥ x)
      (fun x y => ⟨_, aux2_qexp A x y⟩) (fun x y => ⟨_, aux2_qexp B x y⟩) hslater H
    refine ⟨τ, hτ, PosSemidef.of_dotProduct_mulVec_nonneg
      (aux2_isHermitian (aux2_symm_sub_smul hA hB τ)) fun x => ?_⟩
    simpa [aux2_qf_sub_smul] using h x
  · rintro ⟨τ, hτ, h⟩ x hx
    have := h.dotProduct_mulVec_nonneg x
    simp only [star_trivial, aux2_qf_sub_smul] at this
    nlinarith

-- K6: strict S-lemma (Finsler–Yakubovich), no Slater needed

end

section
open Matrix

lemma scal_fwd (τ c s k : ℝ) (hτ : 0 < τ) :
    (-c - 2 * (τ⁻¹ * s)) - τ * (k - τ⁻¹ * (τ⁻¹ * s)) = -c - τ⁻¹ * s - τ * k := by
  field_simp
  ring

lemma scal_zero (c d : ℝ) (hd : 0 ≤ d) (h : ∀ t : ℝ, 0 ≤ -(t * t * c) - 2 * (t * d)) : d = 0 := by
  by_contra hne
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hne)
  set s := |c| + 1 with hs
  have hspos : 0 < s := by positivity
  set t := d / s with ht
  have htpos : 0 < t := div_pos hdpos hspos
  have hts : t * s = d := by rw [ht]; field_simp
  have h1 := h t
  rw [← hts] at h1
  have hcs : 0 < c + 2 * s := by rw [hs]; linarith [neg_abs_le c, abs_nonneg c]
  have : 0 < t * t * (c + 2 * s) := mul_pos (mul_pos htpos htpos) hcs
  linarith

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]

lemma fwd_nonstrict [DecidableEq a] (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ)
    (G : Matrix c a ℝ) (hC : C.IsHermitian) (hE : E ≠ 0) (hFpd : Fbar.PosDef) (hG : G ≠ 0)
    (h : ∀ F ∈ (QuadMatIneq.Petersen.uncSet Fbar : Set (Matrix b c ℝ)),
      (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosSemidef) :
    ∃ lam : ℝ, 0 < lam ∧
      (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosSemidef := by
  have hFbar : Fbar.PosSemidef := hFpd.posSemidef
  have hslater : ∃ y : a ⊕ b → ℝ, 0 < y ⬝ᵥ MB Fbar G *ᵥ y := by
    obtain ⟨j, hj⟩ : ∃ j, G *ᵥ Pi.single j 1 ≠ 0 := by
      by_contra hcon
      simp only [ne_eq, not_exists, not_not] at hcon
      apply hG
      ext i j
      have := congrFun (hcon j) i
      simpa [mulVec_single_one] using this
    refine ⟨Sum.elim (Pi.single j 1) 0, ?_⟩
    rw [qB, dotProduct_zero, sub_zero]
    have := (posDef_iff_dotProduct_mulVec.mp hFpd).2 hj
    rwa [star_trivial] at this
  have hcond : ∀ y : a ⊕ b → ℝ, 0 ≤ y ⬝ᵥ MB Fbar G *ᵥ y → 0 ≤ y ⬝ᵥ MA C E *ᵥ y := by
    intro y hB
    rw [← Sum.elim_comp_inl_inr y] at hB ⊢
    rw [qB] at hB
    rw [qA]
    obtain ⟨F, hF, hFu⟩ := exists_F_of Fbar hFbar G _ _ hB
    have := (h F hF).dotProduct_mulVec_nonneg (y ∘ Sum.inl)
    rw [star_trivial, qf_unc, hFu] at this
    linarith
  obtain ⟨τ, hτ0, hPSD⟩ :=
    (Matrix.sLemma (MA_symm C E hC) (MB_symm Fbar G hFbar.1) hslater).mp hcond
  have hq : ∀ y, 0 ≤ y ⬝ᵥ MA C E *ᵥ y - τ * (y ⬝ᵥ MB Fbar G *ᵥ y) := fun y => by
    have := hPSD.dotProduct_mulVec_nonneg y
    rwa [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul] at this
  have hτ : 0 < τ := by
    rcases hτ0.eq_or_lt with h0 | h0
    swap
    · exact h0
    exfalso
    apply hE
    apply mulVec_injective
    funext w
    rw [zero_mulVec]
    have hd : (Eᵀ *ᵥ (E *ᵥ w)) ⬝ᵥ w = (E *ᵥ w) ⬝ᵥ (E *ᵥ w) := by rw [← dot_mulVec_eq]
    have key := scal_zero ((E *ᵥ w) ⬝ᵥ C *ᵥ (E *ᵥ w)) ((E *ᵥ w) ⬝ᵥ (E *ᵥ w))
      (dot_self_nonneg _) (fun t => by
        have := hq (Sum.elim (t • (E *ᵥ w)) w)
        rw [← h0, qA, zero_mul, sub_zero] at this
        simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hd] at this
        linarith)
    exact dotProduct_self_eq_zero.mp key
  refine ⟨τ⁻¹, inv_pos.mpr hτ, posSemidef_iff_dotProduct_mulVec.mpr
    ⟨herm_target _ _ _ _ _ hC hFbar.1, fun x => ?_⟩⟩
  rw [star_trivial, qf_target, inv_inv]
  have := hq (Sum.elim x (τ⁻¹ • (Eᵀ *ᵥ x)))
  rw [qA, qB] at this
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
  linarith [scal_fwd τ (x ⬝ᵥ C *ᵥ x) ((Eᵀ *ᵥ x) ⬝ᵥ (Eᵀ *ᵥ x))
    ((G *ᵥ x) ⬝ᵥ Fbar *ᵥ (G *ᵥ x)) hτ]

end

section
open Matrix

lemma sLemma_strict_pos {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ y : ι → ℝ, y ≠ 0 → 0 ≤ y ⬝ᵥ B *ᵥ y → 0 < y ⬝ᵥ A *ᵥ y) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ y : ι → ℝ, y ≠ 0 → 0 < y ⬝ᵥ A *ᵥ y - τ * (y ⬝ᵥ B *ᵥ y) := by
  let A' : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ := fromBlocks A 0 (0 : Matrix ι Unit ℝ)ᵀ 0
  let B' : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ := fromBlocks B 0 (0 : Matrix ι Unit ℝ)ᵀ (-1)
  have qA' : ∀ y s, Sum.elim y s ⬝ᵥ A' *ᵥ Sum.elim y s = y ⬝ᵥ A *ᵥ y := fun y s => by
    rw [show A' = fromBlocks A 0 (0 : Matrix ι Unit ℝ)ᵀ 0 from rfl, qf_blocks]
    simp only [transpose_transpose, transpose_zero, zero_mulVec, zero_dotProduct,
      mul_zero, add_zero, dotProduct_zero]
  have qB' : ∀ y s, Sum.elim y s ⬝ᵥ B' *ᵥ Sum.elim y s = y ⬝ᵥ B *ᵥ y - s ⬝ᵥ s := fun y s => by
    rw [show B' = fromBlocks B 0 (0 : Matrix ι Unit ℝ)ᵀ (-1) from rfl, qf_blocks]
    simp only [transpose_transpose, transpose_zero, zero_mulVec, zero_dotProduct,
      mul_zero, add_zero, neg_mulVec, one_mulVec, dotProduct_neg]; ring
  have hA' : A'.IsSymm := isSymm_blocks _ _ _ hA.eq (by simp)
  have hB' : B'.IsSymm := isSymm_blocks _ _ _ hB.eq (by simp)
  have hcond : ∀ z : ι ⊕ Unit → ℝ, z ≠ 0 → 0 ≤ z ⬝ᵥ B' *ᵥ z → 0 < z ⬝ᵥ A' *ᵥ z := by
    intro z hz hBz
    rw [← Sum.elim_comp_inl_inr z] at hz hBz ⊢
    rw [qB'] at hBz
    rw [qA']
    by_cases hy : z ∘ Sum.inl = 0
    · exfalso
      rw [hy] at hBz hz
      simp only [zero_dotProduct] at hBz
      have hs : z ∘ Sum.inr = 0 :=
        dotProduct_self_eq_zero.mp (le_antisymm (by linarith) (dot_self_nonneg _))
      rw [hs] at hz
      exact hz (by simp)
    · exact h _ hy (by linarith [dot_self_nonneg (z ∘ Sum.inr)])
  obtain ⟨τ, -, hPD⟩ := (Matrix.sLemma_strict hA' hB').mp hcond
  have hτ : 0 < τ := by
    have := hPD.diag_pos (i := Sum.inr ())
    simpa [A', B'] using this
  refine ⟨τ, hτ, fun y hy => ?_⟩
  have hz : (Sum.elim y (0 : Unit → ℝ)) ≠ 0 := by
    intro h0; apply hy; have := congrArg (fun z => z ∘ Sum.inl) h0; simpa using this
  have := (posDef_iff_dotProduct_mulVec.mp hPD).2 hz
  rw [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, qA', qB',
    smul_eq_mul] at this
  simpa using this

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]

lemma fwd_strict [DecidableEq a] (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ)
    (G : Matrix c a ℝ) (hC : C.IsHermitian) (hFbar : Fbar.PosSemidef)
    (h : ∀ F ∈ (QuadMatIneq.Petersen.uncSet Fbar : Set (Matrix b c ℝ)),
      (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosDef) :
    ∃ lam : ℝ, 0 < lam ∧ (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosDef := by
  have hcond : ∀ y : a ⊕ b → ℝ, y ≠ 0 → 0 ≤ y ⬝ᵥ MB Fbar G *ᵥ y →
      0 < y ⬝ᵥ MA C E *ᵥ y := by
    intro y hy hB
    rw [← Sum.elim_comp_inl_inr y] at hy hB ⊢
    rw [qB] at hB
    rw [qA]
    obtain ⟨F, hF, hFu⟩ := exists_F_of Fbar hFbar G _ _ hB
    by_cases hx : y ∘ Sum.inl = 0
    · exfalso
      rw [hx, mulVec_zero, zero_dotProduct] at hB
      have hw : y ∘ Sum.inr = 0 :=
        dotProduct_self_eq_zero.mp (le_antisymm (by linarith) (dot_self_nonneg _))
      rw [hx, hw] at hy
      exact hy (by simp)
    · have := (posDef_iff_dotProduct_mulVec.mp (h F hF)).2 hx
      rw [star_trivial, qf_unc, hFu] at this
      linarith
  obtain ⟨τ, hτ, hq⟩ := sLemma_strict_pos (MA_symm C E hC) (MB_symm Fbar G hFbar.1) hcond
  refine ⟨τ⁻¹, inv_pos.mpr hτ, posDef_iff_dotProduct_mulVec.mpr
    ⟨herm_target _ _ _ _ _ hC hFbar.1, fun x hx => ?_⟩⟩
  rw [star_trivial, qf_target, inv_inv]
  have hy : Sum.elim x (τ⁻¹ • (Eᵀ *ᵥ x)) ≠ 0 := by
    intro h0; apply hx; have := congrArg (fun z => z ∘ Sum.inl) h0; simpa using this
  have := hq _ hy
  rw [qA, qB] at this
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
  linarith [scal_fwd τ (x ⬝ᵥ C *ᵥ x) ((Eᵀ *ᵥ x) ⬝ᵥ (Eᵀ *ᵥ x))
    ((G *ᵥ x) ⬝ᵥ Fbar *ᵥ (G *ᵥ x)) hτ]

omit [DecidableEq b] in
lemma herm_unc (C : Matrix a a ℝ) (E : Matrix a b ℝ) (F : Matrix b c ℝ) (G : Matrix c a ℝ)
    (hC : C.IsHermitian) : (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).IsHermitian := by
  apply herm_of_transpose
  rw [transpose_neg, transpose_add, transpose_add, transpose_of_herm hC]
  simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  abel

end

section
open Matrix

lemma scal_rev (l α β γ κ c : ℝ) (hl : 0 < l) (h1 : 0 ≤ l ^ 2 * α - 2 * l * γ + β)
    (h2 : β ≤ κ) : -c - l * α - l⁻¹ * κ ≤ -c - 2 * γ := by
  have h3 : 0 ≤ l⁻¹ * (l ^ 2 * α - 2 * l * γ + β) := mul_nonneg (inv_nonneg.mpr hl.le) h1
  have e : l⁻¹ * (l ^ 2 * α - 2 * l * γ + β) = l * α - 2 * γ + l⁻¹ * β := by
    field_simp
  have h4 : l⁻¹ * β ≤ l⁻¹ * κ := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hl.le)
  linarith

end

section
open Matrix
variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]

omit [DecidableEq b] in
lemma rev_le (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ) (G : Matrix c a ℝ)
    (lam : ℝ) (hlam : 0 < lam) (F : Matrix b c ℝ) (hF : F ∈ (QuadMatIneq.Petersen.uncSet Fbar :
      Set (Matrix b c ℝ))) (x : a → ℝ) :
    x ⬝ᵥ (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))) *ᵥ x ≤
      x ⬝ᵥ (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)) *ᵥ x := by
  rw [qf_target, qf_unc]
  have hF' : (F *ᵥ (G *ᵥ x)) ⬝ᵥ (F *ᵥ (G *ᵥ x)) ≤ (G *ᵥ x) ⬝ᵥ Fbar *ᵥ (G *ᵥ x) := by
    have := hF.dotProduct_mulVec_nonneg (G *ᵥ x)
    rw [star_trivial, sub_mulVec, dotProduct_sub, qf_transpose_mul] at this
    linarith
  have h1 := dot_self_nonneg (lam • (Eᵀ *ᵥ x) - F *ᵥ (G *ᵥ x))
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct, smul_dotProduct,
    dotProduct_smul, dotProduct_smul, dotProduct_comm (F *ᵥ (G *ᵥ x)) (Eᵀ *ᵥ x)] at h1
  simp only [smul_eq_mul] at h1
  exact scal_rev lam _ _ _ _ _ hlam (by linarith [h1]) hF'

omit [DecidableEq b] in
lemma rev_nonstrict (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ)
    (G : Matrix c a ℝ) (hC : C.IsHermitian) (lam : ℝ) (hlam : 0 < lam)
    (hPSD : (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosSemidef) :
    ∀ F ∈ (QuadMatIneq.Petersen.uncSet Fbar : Set (Matrix b c ℝ)),
      (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosSemidef := fun F hF =>
  posSemidef_iff_dotProduct_mulVec.mpr ⟨herm_unc _ _ _ _ hC, fun x => by
    have := hPSD.dotProduct_mulVec_nonneg x
    rw [star_trivial] at this ⊢
    exact le_trans this (rev_le C E Fbar G lam hlam F hF x)⟩

omit [DecidableEq b] in
lemma rev_strict (C : Matrix a a ℝ) (E : Matrix a b ℝ) (Fbar : Matrix c c ℝ) (G : Matrix c a ℝ)
    (hC : C.IsHermitian) (lam : ℝ) (hlam : 0 < lam)
    (hPD : (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosDef) :
    ∀ F ∈ (QuadMatIneq.Petersen.uncSet Fbar : Set (Matrix b c ℝ)),
      (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosDef := fun F hF =>
  posDef_iff_dotProduct_mulVec.mpr ⟨herm_unc _ _ _ _ hC, fun x hx => by
    have := (posDef_iff_dotProduct_mulVec.mp hPD).2 hx
    rw [star_trivial] at this ⊢
    exact lt_of_lt_of_le this (rev_le C E Fbar G lam hlam F hF x)⟩

end

section

open QuadMatIneq.Petersen in
open Matrix in
theorem solution {n p q : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (E : Matrix (Fin n) (Fin p) ℝ) (Fbar : Matrix (Fin q) (Fin q) ℝ)
    (G : Matrix (Fin q) (Fin n) ℝ) (hC : C.IsHermitian) (hFbar : Fbar.PosSemidef) :
    ((∀ F ∈ (uncSet Fbar : Set (Matrix (Fin p) (Fin q) ℝ)),
        (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosDef) ↔
      ∃ lam : ℝ, 0 < lam ∧ (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosDef) ∧
    (E ≠ 0 → Fbar.PosDef → G ≠ 0 →
      ((∀ F ∈ (uncSet Fbar : Set (Matrix (Fin p) (Fin q) ℝ)),
          (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosSemidef) ↔
        ∃ lam : ℝ, 0 < lam ∧
          (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosSemidef)) := by
  refine ⟨⟨fwd_strict C E Fbar G hC hFbar,
    fun ⟨lam, hlam, h⟩ =>
      rev_strict C E Fbar G hC lam hlam h⟩,
    fun hE hFpd hG => ⟨fwd_nonstrict C E Fbar G hC
      hE hFpd hG, fun ⟨lam, hlam, h⟩ =>
        rev_nonstrict C E Fbar G hC lam hlam h⟩⟩

end
