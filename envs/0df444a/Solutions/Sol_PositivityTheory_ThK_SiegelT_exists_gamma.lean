-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.exists_gamma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:53:00.932561+00:00
-- url     : https://prove2.me/submissions/c15a6eea-7090-4429-8310-37c3dc87d8f9

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg
import Theorems.Thm_P2M_PositivityTheory_ThK_SiegelT_map_mul__f92fda10766b
import Theorems.Thm_P2M_PositivityTheory_ThK_SiegelT_map_one__a6a1ccb9bfd7
import Theorems.Thm_PositivityTheory_ThK_SiegelT_exists_UG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β ν ν' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν]
  [Fintype ν'] [DecidableEq ν']
private theorem fromBlocks_transpose_dbl_map_eq_dbl {J : Matrix β β E} {ey fx : Matrix β ν E} {m1 m2 : Matrix ν β E}
    (h1e : m1 * ey = 1) (h1f : m1 * fx = 0) (h2e : m2 * ey = 0) (h2f : m2 * fx = 1)
    (hJ : J = m1ᵀ * m2.map c - m2ᵀ * m1.map c) :
    (fromBlocks 1 (-(fx * m2)) (-(fx * m1)) (fx * m1 - ey * m2) : Matrix (β ⊕ β) (β ⊕ β) E)ᵀ * dbl J *
      (fromBlocks 1 (-(fx * m2)) (-(fx * m1)) (fx * m1 - ey * m2) : Matrix (β ⊕ β) (β ⊕ β) E).map c = dbl J := by
  have mneg : ∀ {a b : Type} (A : Matrix a b E), (-A).map c = -(A.map c) := fun A => by ext; simp
  have msub : ∀ {a b : Type} (A B : Matrix a b E), (A - B).map c = A.map c - B.map c := fun A B => by ext; simp
  have c1e : m1.map c * ey.map c = 1 := by rw [← map_mul', h1e, map_one']
  have c1f : m1.map c * fx.map c = 0 := by rw [← map_mul', h1f]; ext; simp
  have c2e : m2.map c * ey.map c = 0 := by rw [← map_mul', h2e]; ext; simp
  have c2f : m2.map c * fx.map c = 1 := by rw [← map_mul', h2f, map_one']
  have t1e : eyᵀ * m1ᵀ = 1 := by rw [← Matrix.transpose_mul, h1e, Matrix.transpose_one]
  have t1f : fxᵀ * m1ᵀ = 0 := by rw [← Matrix.transpose_mul, h1f, Matrix.transpose_zero]
  have t2e : eyᵀ * m2ᵀ = 0 := by rw [← Matrix.transpose_mul, h2e, Matrix.transpose_zero]
  have t2f : fxᵀ * m2ᵀ = 1 := by rw [← Matrix.transpose_mul, h2f, Matrix.transpose_one]
  have c1e' : ∀ {k : Type} (Z : Matrix ν k E), m1.map c * (ey.map c * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, c1e, Matrix.one_mul]
  have c1f' : ∀ {k : Type} (Z : Matrix ν k E), m1.map c * (fx.map c * Z) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, c1f, Matrix.zero_mul]
  have c2e' : ∀ {k : Type} (Z : Matrix ν k E), m2.map c * (ey.map c * Z) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, c2e, Matrix.zero_mul]
  have c2f' : ∀ {k : Type} (Z : Matrix ν k E), m2.map c * (fx.map c * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, c2f, Matrix.one_mul]
  have t1e' : ∀ {k : Type} (Z : Matrix ν k E), eyᵀ * (m1ᵀ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, t1e, Matrix.one_mul]
  have t1f' : ∀ {k : Type} (Z : Matrix ν k E), fxᵀ * (m1ᵀ * Z) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, t1f, Matrix.zero_mul]
  have t2e' : ∀ {k : Type} (Z : Matrix ν k E), eyᵀ * (m2ᵀ * Z) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, t2e, Matrix.zero_mul]
  have t2f' : ∀ {k : Type} (Z : Matrix ν k E), fxᵀ * (m2ᵀ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, t2f, Matrix.one_mul]
  subst hJ
  simp only [Matrix.fromBlocks_map, map_one', mneg, msub, map_mul']
  simp only [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_one, Matrix.transpose_neg,
    Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_zero]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_assoc, neg_neg, neg_zero,
      add_zero, zero_add, sub_zero, zero_sub, c1e, c1f, c2e, c2f, t1e, t1f, t2e, t2f, c1e', c1f', c2e', c2f',
      t1e', t1f', t2e', t2f'] <;> abel
private theorem fromBlocks_mul_diagCols_eq {ey fx : Matrix β ν E} {m1 m2 : Matrix ν β E} (hsum : ey * m1 + fx * m2 = 1) :
    (fromBlocks 1 (-(fx * m2)) (-(fx * m1)) (fx * m1 - ey * m2) : Matrix (β ⊕ β) (β ⊕ β) E) *
      (diagCols β : Matrix (β ⊕ β) β E) = (fromBlocks ey 0 0 ey : Matrix (β ⊕ β) (ν ⊕ ν) E) * fromRows m1 (-m2) := by
  simp only [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_neg, add_zero,
    zero_add]
  congr 1
  · rw [← hsum]; abel
  · abel
end PositivityTheory.ThK.SiegelT
end
end

set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β ν ν' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν]
  [Fintype ν'] [DecidableEq ν']
namespace PositivityTheory.ThK.SiegelT
theorem _root_.solution (hc : ∀ z, c (c z) = z) {J : Matrix β β E} (hsk : ∀ i j, c (J j i) = -J i j) (hJ : IsUnit J.det)
    {Cy : Matrix β ν E} (hL : IsLagr c J Cy) :
    ∃ (γ : UG c (dbl J)) (s : Matrix (ν ⊕ ν) β E) (s' : Matrix β (ν ⊕ ν) E), s * s' = 1 ∧ s' * s = 1 ∧
      ((γ : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) * (diagCols β : Matrix (β ⊕ β) β E) =
        (fromBlocks Cy 0 0 Cy : Matrix (β ⊕ β) (ν ⊕ ν) E) * s := by
  obtain ⟨hy, Cx, M, hx, hPM, hMP⟩ := hL
  obtain ⟨m1, m2, rfl⟩ : ∃ m1 m2, M = fromRows m1 m2 := ⟨M.toRows₁, M.toRows₂, (Matrix.fromRows_toRows M).symm⟩
  rw [Matrix.fromCols_mul_fromRows] at hPM
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hMP
  obtain ⟨k1e, k1f, k2e, k2f⟩ := hMP
  have madd : ∀ {a b : Type} (X Y : Matrix a b E), (X + Y).map c = X.map c + Y.map c := fun X Y => by ext; simp
  have hcc : ∀ {a b : Type} (X : Matrix a b E), (X.map c).map c = X := fun X => by ext; simp [hc]
  have herm : ∀ {m n : Type} (P : Matrix β m E) (Q : Matrix β n E),
      Qᵀ * J * P.map c = -((Pᵀ * J * Q.map c).map c)ᵀ := by
    intro m n P Q
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, map_sum, map_mul, hc,
      hsk, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hJinv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJ
  have hPMc : Cy.map c * m1.map c + Cx.map c * m2.map c = 1 := by
    rw [← map_mul', ← map_mul', ← madd, hPM, map_one']
  obtain ⟨A, hA⟩ : ∃ A : Matrix ν ν E, A = Cyᵀ * J * Cx.map c := ⟨_, rfl⟩
  obtain ⟨Ai, hAi⟩ : ∃ Ai : Matrix ν ν E, Ai = m2.map c * J⁻¹ * m1ᵀ := ⟨_, rfl⟩
  have hAAi : A * Ai = 1 := by
    have e1 : Cx.map c * m2.map c = 1 - Cy.map c * m1.map c := by rw [← hPMc]; abel
    calc A * Ai = Cyᵀ * J * (Cx.map c * m2.map c) * J⁻¹ * m1ᵀ := by rw [hA, hAi]; simp only [Matrix.mul_assoc]
      _ = Cyᵀ * (J * J⁻¹) * m1ᵀ - Cyᵀ * J * Cy.map c * m1.map c * J⁻¹ * m1ᵀ := by
          rw [e1]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by
          simp only [hJinv, hy, Matrix.mul_one, Matrix.zero_mul, sub_zero]
          rw [← Matrix.transpose_mul, k1e, Matrix.transpose_one]
  have hAiA : Ai * A = 1 := by
    first
    | exact mul_eq_one_comm.mp hAAi
    | (rw [← Matrix.inv_eq_right_inv hAAi]; exact Matrix.nonsing_inv_mul A (Matrix.isUnit_det_of_right_inverse hAAi))
  obtain ⟨f, hf⟩ : ∃ f : Matrix β ν E, f = Cx * Ai.map c := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n2 : Matrix ν β E, n2 = A.map c * m2 := ⟨_, rfl⟩
  have hf1 : m1 * f = 0 := by rw [hf, ← Matrix.mul_assoc, k1f, Matrix.zero_mul]
  have hn2e : n2 * Cy = 0 := by rw [hn2, Matrix.mul_assoc, k2e, Matrix.mul_zero]
  have hn2f : n2 * f = 1 := by
    rw [hn2, hf, Matrix.mul_assoc, ← Matrix.mul_assoc m2, k2f, Matrix.one_mul, ← map_mul', hAAi, map_one']
  have hsum : Cy * m1 + f * n2 = 1 := by
    have h' : f * n2 = Cx * m2 := by
      rw [hf, hn2, Matrix.mul_assoc, ← Matrix.mul_assoc (Ai.map c), ← map_mul', hAiA, map_one', Matrix.one_mul]
    rw [h']; exact hPM
  have hfc : f.map c = Cx.map c * Ai := by rw [hf, map_mul', hcc]
  have hef : Cyᵀ * J * f.map c = 1 := by rw [hfc, ← Matrix.mul_assoc, ← hA, hAAi]
  have hfe : fᵀ * J * Cy.map c = -1 := by rw [herm Cy f, hef, map_one', Matrix.transpose_one]
  have hff : fᵀ * J * f.map c = 0 := by
    rw [hfc, hf, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J (Cx.map c) Ai, ← Matrix.mul_assoc Cxᵀ (J * Cx.map c) Ai,
      ← Matrix.mul_assoc Cxᵀ J (Cx.map c), hx, Matrix.zero_mul, Matrix.mul_zero]
  have hJform : J = m1ᵀ * n2.map c - n2ᵀ * m1.map c := by
    calc J = (Cy * m1 + f * n2)ᵀ * J * (Cy * m1 + f * n2).map c := by
          rw [hsum, Matrix.transpose_one, map_one', Matrix.one_mul, Matrix.mul_one]
      _ = m1ᵀ * (Cyᵀ * J * Cy.map c) * m1.map c + m1ᵀ * (Cyᵀ * J * f.map c) * n2.map c +
            n2ᵀ * (fᵀ * J * Cy.map c) * m1.map c + n2ᵀ * (fᵀ * J * f.map c) * n2.map c := by
          rw [madd, map_mul', map_mul']
          simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
          abel
      _ = m1ᵀ * n2.map c - n2ᵀ * m1.map c := by
          rw [hy, hef, hfe, hff]
          simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, zero_add,
            add_zero]
          abel
  have hdetH : IsUnit (dbl J).det := by
    show IsUnit (Matrix.fromBlocks J 0 0 (-J)).det
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact hJ.mul ((isUnit_neg_one.pow _).mul hJ)
  obtain ⟨u, hu⟩ := exists_UG hdetH (fromBlocks_transpose_dbl_map_eq_dbl k1e hf1 hn2e hn2f hJform)
  refine ⟨u, fromRows m1 (-n2), fromCols Cy (-f), ?_, ?_, ?_⟩
  · simp only [Matrix.fromRows_mul_fromCols, Matrix.mul_neg, Matrix.neg_mul, neg_neg, k1e, hf1, hn2e, hn2f,
      neg_zero, Matrix.fromBlocks_one]
  · simp only [Matrix.fromCols_mul_fromRows, Matrix.neg_mul, Matrix.mul_neg, neg_neg]; exact hsum
  · rw [hu]; exact fromBlocks_mul_diagCols_eq hsum
end PositivityTheory.ThK.SiegelT
