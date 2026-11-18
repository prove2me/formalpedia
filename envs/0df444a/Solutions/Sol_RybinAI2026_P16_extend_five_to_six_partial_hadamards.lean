-- Prove2me | solution 1 for RybinAI2026.P16.extend_five_to_six_partial_hadamards
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T14:49:31.799943+00:00
-- url     : https://prove2.me/submissions/b73bd632-ddcc-434e-9217-b6e18f1b639b

import Mathlib
import Theorems.Thm_OAI_MUB6_fourier_and_family_bound

/-! `extend_five_to_six_partial_hadamards` holds vacuously: five mutually unbiased six-by-five
partial Hadamard matrices, together with the standard basis, would give six mutually unbiased
bases of `ℂ⁶`, which `OAI.MUB6.fourier_and_family_bound` (at most five) rules out. -/

/-! Bridge lemmas: matrix-coordinate (partial) Hadamard and MUB families give `Attainable`. -/

namespace OAI.MUB6.P2MBridge

open Matrix
open scoped ComplexConjugate Matrix

/-- `1/√6`. -/
noncomputable def sc : ℂ := ((Real.sqrt 6 : ℝ) : ℂ)⁻¹

lemma conj_sc_mul_sc : conj sc * sc = (1 / 6 : ℂ) := by
  rw [mul_comm, Complex.mul_conj, sc, Complex.normSq_inv, Complex.normSq_ofReal, ← sq,
    Real.sq_sqrt (by norm_num)]
  push_cast; ring

lemma normSq_sc : Complex.normSq sc = 1 / 6 := by
  rw [sc, Complex.normSq_inv, Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)]
  norm_num

lemma normSq_inner_symm (x y : Space) :
    Complex.normSq (inner ℂ x y) = Complex.normSq (inner ℂ y x) := by
  rw [← inner_conj_symm, Complex.normSq_conj]

/-- A full orthonormal-basis pair whose leading `5 × 5` overlaps are unbiased is unbiased. -/
lemma pair_full (b c : MUB6.Basis)
    (h : ∀ i j : Fin 5, Complex.normSq (inner ℂ (b i.castSucc) (c j.castSucc)) = 1 / 6) :
    ∀ i j, Complex.normSq (inner ℂ (b i) (c j)) = 1 / 6 := by
  have row : ∀ i, ∑ j, Complex.normSq (inner ℂ (b i) (c j)) = 1 := by
    intro i
    have := c.sum_sq_norm_inner_left (b i)
    simpa [Complex.sq_norm, b.orthonormal.1 i] using this
  have col : ∀ j, ∑ i, Complex.normSq (inner ℂ (b i) (c j)) = 1 := by
    intro j
    have := b.sum_sq_norm_inner_right (c j)
    simpa [Complex.sq_norm, c.orthonormal.1 j] using this
  have h1 : ∀ i : Fin 5, Complex.normSq (inner ℂ (b i.castSucc) (c (Fin.last 5))) = 1 / 6 := by
    intro i
    have := row i.castSucc
    rw [Fin.sum_univ_castSucc] at this
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    rw [show (Fin.last 5 : Fin 6) = 5 from rfl]; linarith
  have h2 : ∀ j : Fin 5, Complex.normSq (inner ℂ (b (Fin.last 5)) (c j.castSucc)) = 1 / 6 := by
    intro j
    have := col j.castSucc
    rw [Fin.sum_univ_castSucc] at this
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    rw [show (Fin.last 5 : Fin 6) = 5 from rfl]; linarith
  have h3 : Complex.normSq (inner ℂ (b (Fin.last 5)) (c (Fin.last 5))) = 1 / 6 := by
    have := row (Fin.last 5)
    rw [Fin.sum_univ_castSucc] at this
    simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    rw [show (Fin.last 5 : Fin 6) = 5 from rfl]; linarith
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact h3
    | cast j => exact h2 j
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact h1 i
    | cast j => exact h i j

/-- The `j`-th column of `A / √6`, as a vector of `ℂ⁶`. -/
noncomputable def pcol (A : Matrix (Fin 6) (Fin 5) ℂ) (j : Fin 5) : Space :=
  WithLp.toLp 2 (fun k => sc * A k j)

lemma inner_pcol (A A' : Matrix (Fin 6) (Fin 5) ℂ) (i j : Fin 5) :
    inner ℂ (pcol A i) (pcol A' j) = (1 / 6 : ℂ) * (Aᴴ * A') i j := by
  rw [pcol, pcol, EuclideanSpace.inner_toLp_toLp, ← conj_sc_mul_sc]
  simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum,
    Pi.star_apply, star_mul', Complex.star_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma inner_std_pcol (A : Matrix (Fin 6) (Fin 5) ℂ) (i : Fin 6) (j : Fin 5) :
    inner ℂ (EuclideanSpace.basisFun (Fin 6) ℂ i) (pcol A j) = sc * A i j := by
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  simp [pcol]

lemma orthonormal_pcol (A : Matrix (Fin 6) (Fin 5) ℂ)
    (hA : Aᴴ * A = (6 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ)) : Orthonormal ℂ (pcol A) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_pcol, hA, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- Complete the columns of a six-by-five partial Hadamard matrix to an orthonormal basis. -/
lemma exists_basis_ext (A : Matrix (Fin 6) (Fin 5) ℂ)
    (hA : Aᴴ * A = (6 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ)) :
    ∃ b : MUB6.Basis, ∀ j : Fin 5, b j.castSucc = pcol A j := by
  classical
  let v : Fin 6 → Space := Fin.lastCases 0 (pcol A)
  have hv : Orthonormal ℂ ((Set.range (Fin.castSucc : Fin 5 → Fin 6)).restrict v) := by
    have hon := orthonormal_pcol A hA
    rw [orthonormal_iff_ite] at hon ⊢
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    change inner ℂ (v i.castSucc) (v j.castSucc) = _
    simp only [v, Fin.lastCases_castSucc]
    rw [hon i j]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg]
      intro e
      exact h (Fin.castSucc_injective _ (congrArg Subtype.val e))
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp) (v := v) (s := Set.range (Fin.castSucc : Fin 5 → Fin 6))
  exact ⟨b, fun j => by rw [hb _ ⟨j, rfl⟩]; simp [v]⟩

/-- Master bridge: `n` mutually unbiased six-by-five partial Hadamard matrices, with the
entry-modulus equations on the first five rows, give `n + 1` mutually unbiased bases. -/
theorem attainable_of_partial {n : ℕ} (A : Fin n → Matrix (Fin 6) (Fin 5) ℂ)
    (hG : ∀ r, (A r)ᴴ * A r = (6 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ))
    (hE : ∀ r, ∀ i j : Fin 5, Complex.normSq (A r i.castSucc j) = 1)
    (hX : ∀ r s, r < s → ∀ i j : Fin 5, Complex.normSq (((A r)ᴴ * A s) i j) = 6) :
    Attainable (n + 1) := by
  choose b hb using fun r => exists_basis_ext (A r) (hG r)
  let e : MUB6.Basis := EuclideanSpace.basisFun (Fin 6) ℂ
  have key0 : ∀ r i j, Complex.normSq (inner ℂ (e i) (b r j)) = 1 / 6 := by
    intro r
    apply pair_full
    intro i j
    rw [hb, inner_std_pcol, Complex.normSq_mul, normSq_sc, hE]
    ring
  have keyrs : ∀ r s, r < s → ∀ i j, Complex.normSq (inner ℂ (b r i) (b s j)) = 1 / 6 := by
    intro r s hrs
    apply pair_full
    intro i j
    rw [hb, hb, inner_pcol, Complex.normSq_mul, hX r s hrs]
    norm_num
  have keyne : ∀ r s, r ≠ s → ∀ i j, Complex.normSq (inner ℂ (b r i) (b s j)) = 1 / 6 := by
    intro r s hrs i j
    rcases lt_or_gt_of_ne hrs with h | h
    · exact keyrs r s h i j
    · rw [normSq_inner_symm]; exact keyrs s r h j i
  refine ⟨Fin.cons e b, ?_⟩
  intro r s hrs i j
  induction r using Fin.cases with
  | zero =>
    induction s using Fin.cases with
    | zero => exact absurd rfl hrs
    | succ s => simpa using key0 s i j
  | succ r =>
    induction s using Fin.cases with
    | zero => simpa [normSq_inner_symm (b r i)] using key0 r j i
    | succ s =>
      simpa using keyne r s (fun h => hrs (by rw [h])) i j


end OAI.MUB6.P2MBridge

open Matrix
open scoped ComplexConjugate Matrix

theorem solution
    (A : Fin 5 → Matrix (Fin 6) (Fin 5) ℂ)
    (hA :
      (∀ r, (A r)ᴴ * A r = (6 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ)) ∧
      (∀ r, ∀ i j : Fin 5, Complex.normSq (A r i.castSucc j) = 1) ∧
      (∀ r s, r < s → ∀ i j : Fin 5,
        Complex.normSq (((A r)ᴴ * A s) i j) = 6)) :
    ∃ B : Fin 6 → Matrix (Fin 6) (Fin 5) ℂ,
      (∀ r, (B r)ᴴ * B r = (6 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ)) ∧
      (∀ r, ∀ i j : Fin 5, Complex.normSq (B r i.castSucc j) = 1) ∧
      (∀ r s, r < s → ∀ i j : Fin 5,
        Complex.normSq (((B r)ᴴ * B s) i j) = 6) := by
  exfalso
  have h6 := OAI.MUB6.fourier_and_family_bound.2 _
    (OAI.MUB6.P2MBridge.attainable_of_partial A hA.1 hA.2.1 hA.2.2)
  omega
