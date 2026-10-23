-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P05.symplecticRows_completion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:32:18.313988+00:00
-- url     : https://prove2.me/submissions/72ded8f0-5405-4050-a527-e99dc40e604b

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_symplectic_bases_pairing

noncomputable section

open scoped ComplexOrder
open Matrix QAlgorithms.Papers.Independent.Dependency50.P10
  QAlgorithms.Papers.Independent.Frontier18.P05

namespace X5SymplecticRows

lemma mul_mul_transpose_apply {m m' k : Type*} [Fintype k]
    (A : Matrix m k ℝ) (M : Matrix k k ℝ) (B : Matrix m' k ℝ) (i : m) (j : m') :
    (A * M * Bᵀ) i j = A i ⬝ᵥ (M *ᵥ B j) := by
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma sigma_transpose (n : ℕ) : (sigma n)ᵀ = -sigma n := by
  simp [sigma, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

lemma sigma_mul_self (n : ℕ) : sigma n * sigma n = -1 := by
  simp [sigma, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]

lemma skew_dot {k : Type*} [Fintype k] (Ω : Matrix k k ℝ) (hΩ : Ωᵀ = -Ω) (x y : k → ℝ) :
    x ⬝ᵥ (Ω *ᵥ y) = -(y ⬝ᵥ (Ω *ᵥ x)) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hΩ, Matrix.neg_mulVec,
    neg_dotProduct, dotProduct_comm]

end X5SymplecticRows

open X5SymplecticRows in
theorem solution {n q : ℕ} (hn : 0 < n)
    (omega : Matrix (Phase q) (Phase q) ℝ)
    (hOmega : IsEnvironmentalForm omega)
    (s1 : Matrix (Phase n) (Phase n) ℝ)
    (s2 : Matrix (Phase n) (Phase q) ℝ)
    (hRows : s1 * sigma n * s1.transpose + s2 * omega * s2.transpose = sigma n) :
    ∃ s3 : Matrix (Phase q) (Phase n) ℝ,
      ∃ s4 : Matrix (Phase q) (Phase q) ℝ,
        let S := Matrix.fromBlocks s1 s2 s3 s4
        let form := Matrix.fromBlocks (sigma n) 0 0 omega
        S * form * S.transpose = form := by
  obtain ⟨e, he⟩ := hOmega
  set Ω : Matrix (Phase n ⊕ Phase q) (Phase n ⊕ Phase q) ℝ :=
    Matrix.fromBlocks (sigma n) 0 0 omega with hΩdef
  have hωt : omegaᵀ = -omega := by
    rw [he, Matrix.transpose_submatrix, sigma_transpose]; rfl
  have hωω : omega * omega = -1 := by
    rw [he, Matrix.submatrix_mul_equiv, sigma_mul_self]
    ext i j; simp [Matrix.one_apply]
  have hΩt : Ωᵀ = -Ω := by
    simp [Ω, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg, sigma_transpose, hωt]
  have hΩΩ : Ω * Ω = -1 := by
    simp [Ω, Matrix.fromBlocks_multiply, sigma_mul_self, hωω, Matrix.fromBlocks_neg,
      ← Matrix.fromBlocks_one]
  -- the bilinear form
  let B : LinearMap.BilinForm ℝ (Phase n ⊕ Phase q → ℝ) := Matrix.toBilin' Ω
  have hB : ∀ x y, B x y = x ⬝ᵥ (Ω *ᵥ y) := fun x y => Matrix.toBilin'_apply' Ω x y
  have hBskew : ∀ x y, B x y = -B y x := fun x y => by rw [hB, hB, skew_dot Ω hΩt]
  have hBsep : ∀ x, (∀ y, B x y = 0) → x = 0 := by
    intro x hx
    have h1 : Ωᵀ *ᵥ x = 0 := by
      have := hx (Ωᵀ *ᵥ x)
      rw [hB, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at this
      exact dotProduct_self_eq_zero.mp this
    have : Ωᵀ *ᵥ (Ωᵀ *ᵥ x) = -x := by
      rw [Matrix.mulVec_mulVec, hΩt, neg_mul_neg, hΩΩ, Matrix.neg_mulVec, Matrix.one_mulVec]
    rw [h1, Matrix.mulVec_zero] at this
    exact (neg_eq_zero.mp this.symm)
  -- the prescribed rows
  let r : Phase n → (Phase n ⊕ Phase q → ℝ) := fun i => Sum.elim (s1 i) (s2 i)
  have hrr : ∀ i j, B (r i) (r j) = sigma n i j := by
    intro i j
    have h := congrFun (congrFun hRows i) j
    rw [Matrix.add_apply, mul_mul_transpose_apply, mul_mul_transpose_apply] at h
    rw [hB, ← h]
    simp only [r, Ω, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
      sumElim_dotProduct_sumElim, Sum.elim_comp_inl, Sum.elim_comp_inr]
  -- the map to the pairings with the rows, and its kernel
  let φ : (Phase n ⊕ Phase q → ℝ) →ₗ[ℝ] (Phase n → ℝ) := LinearMap.pi fun i => B (r i)
  have hφ : ∀ y i, φ y i = B (r i) y := fun y i => rfl
  let lift : (Phase n → ℝ) → (Phase n ⊕ Phase q → ℝ) :=
    fun t => ∑ j, (-(sigma n *ᵥ t) j) • r j
  have hlift : ∀ t, φ (lift t) = t := by
    intro t
    funext i
    rw [hφ]
    simp only [lift, map_sum, map_smul, hrr, smul_eq_mul]
    have : sigma n *ᵥ (-(sigma n *ᵥ t)) = t := by
      rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, sigma_mul_self, Matrix.neg_mulVec,
        Matrix.one_mulVec, neg_neg]
    have h2 := congrFun this i
    rw [← h2]
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  set C := LinearMap.ker φ with hC
  have hmemC : ∀ y, y ∈ C ↔ ∀ i, B (r i) y = 0 := by
    intro y
    rw [hC, LinearMap.mem_ker, funext_iff]
    rfl
  have hsurj : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact fun t => ⟨lift t, hlift t⟩
  have hdimC : Module.finrank ℝ C = 2 * q := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card] at h
    simp only [Phase, Fintype.card_sum, Fintype.card_fin] at h
    rw [← hC] at h
    rw [two_mul]; exact Nat.add_left_cancel h
  -- vectors of `C` pairing trivially with `C` are zero
  have hCsep : ∀ c ∈ C, (∀ c' ∈ C, B c c' = 0) → c = 0 := by
    intro c hc hcc
    apply hBsep
    intro y
    have hyw : y - lift (φ y) ∈ C := by
      rw [hC, LinearMap.mem_ker, map_sub, hlift, sub_self]
    have h1 : B c (y - lift (φ y)) = 0 := hcc _ hyw
    have h2 : B c (lift (φ y)) = 0 := by
      simp only [lift, map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hBskew, (hmemC c).mp hc j, neg_zero, mul_zero]
    rw [map_sub, h2, sub_zero] at h1
    exact h1
  -- a symplectic basis of `C`, with Gram matrix `omega`
  obtain ⟨g, hgC, hgg⟩ : ∃ g : Phase q → (Phase n ⊕ Phase q → ℝ),
      (∀ a, g a ∈ C) ∧ ∀ a b, B (g a) (g b) = omega a b := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      exact ⟨fun a => isEmptyElim a, fun a => isEmptyElim a, fun a => isEmptyElim a⟩
    · let BC : LinearMap.BilinForm ℝ C := B.restrict C
      have hBCalt : BC.IsAlt := by
        intro x
        have := hBskew x x
        change B x x = 0
        linarith
      have hBCnd : BC.Nondegenerate := by
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩
        · apply Subtype.ext
          exact hCsep x x.2 fun c' hc' => hx ⟨c', hc'⟩
        · apply Subtype.ext
          refine hCsep x x.2 fun c' hc' => ?_
          have := hx ⟨c', hc'⟩
          change B c' x = 0 at this
          rw [hBskew, this, neg_zero]
      obtain ⟨⟨b, hb⟩, -, -⟩ :=
        QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_bases_pairing q hq C hdimC
          BC hBCalt hBCnd
      refine ⟨fun a => (b (e a) : Phase n ⊕ Phase q → ℝ), fun a => (b (e a)).2, ?_⟩
      intro a a'
      have := hb (e a) (e a')
      rw [he]
      exact this
  -- assemble the symplectic matrix row by row
  let R : Phase n ⊕ Phase q → (Phase n ⊕ Phase q → ℝ) := Sum.elim r g
  let S : Matrix (Phase n ⊕ Phase q) (Phase n ⊕ Phase q) ℝ := Matrix.of R
  refine ⟨S.toBlocks₂₁, S.toBlocks₂₂, ?_⟩
  have hS : Matrix.fromBlocks s1 s2 S.toBlocks₂₁ S.toBlocks₂₂ = S := by
    have h11 : S.toBlocks₁₁ = s1 := by ext i j; rfl
    have h12 : S.toBlocks₁₂ = s2 := by ext i j; rfl
    rw [← h11, ← h12, Matrix.fromBlocks_toBlocks]
  show Matrix.fromBlocks s1 s2 S.toBlocks₂₁ S.toBlocks₂₂ * Ω *
      (Matrix.fromBlocks s1 s2 S.toBlocks₂₁ S.toBlocks₂₂)ᵀ = Ω
  rw [hS]
  ext x y
  rw [mul_mul_transpose_apply, ← hB]
  change B (R x) (R y) = Ω x y
  rcases x with i | a <;> rcases y with j | b
  · exact hrr i j
  · change B (r i) (g b) = 0
    exact (hmemC _).mp (hgC b) i
  · change B (g a) (r j) = 0
    rw [hBskew, (hmemC _).mp (hgC a) j, neg_zero]
  · exact hgg a b
