-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.orthogonal_basis_noise
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:38:46.967674+00:00
-- url     : https://prove2.me/submissions/6e42b95e-c4c0-4a20-8c34-5da7de8d4c86

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]


open Matrix

theorem x8_complete [Nonempty A] (T : UnitaryBasis A K) (i j l m : A) :
    ∑ k, T.matrix k i j * star (T.matrix k l m) =
      if (i, j) = (l, m) then (Fintype.card A : ℂ) else 0 := by
  have hcard : Fintype.card K = Fintype.card (A × A) := by
    rw [T.cardinality, Fintype.card_prod, sq]
  let e : K ≃ A × A := Fintype.equivOfCardEq hcard
  obtain ⟨W, hW⟩ : ∃ W : Matrix (A × A) (A × A) ℂ, ∀ p q, W p q = T.matrix (e.symm q) p.1 p.2 :=
    ⟨Matrix.of fun p q => T.matrix (e.symm q) p.1 p.2, fun _ _ => rfl⟩
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hWW : Wᴴ * W = (Fintype.card A : ℂ) • 1 := by
    ext q q'
    have := T.orthogonal (e.symm q) (e.symm q')
    simp only [trace, diag, mul_apply, conjTranspose_apply] at this
    rw [mul_apply, Matrix.smul_apply, one_apply]
    simp only [conjTranspose_apply, hW, Fintype.sum_prod_type]
    rw [Finset.sum_comm] at this
    rw [this]
    by_cases h : q = q' <;> simp [h, e.symm.injective.eq_iff]
  have h1 : ((Fintype.card A : ℂ)⁻¹ • Wᴴ) * W = 1 := by
    rw [smul_mul_assoc, hWW, smul_smul, inv_mul_cancel₀ hd, one_smul]
  have h2 := mul_eq_one_comm.1 h1
  rw [mul_smul_comm] at h2
  have h3 : W * Wᴴ = (Fintype.card A : ℂ) • 1 := by
    have := congrArg (fun M => (Fintype.card A : ℂ) • M) h2
    simp only [smul_smul, mul_inv_cancel₀ hd, one_smul] at this
    exact this
  have := congrFun (congrFun h3 (i, j)) (l, m)
  rw [mul_apply, Matrix.smul_apply, one_apply] at this
  simp only [conjTranspose_apply, hW] at this
  rw [← e.symm.sum_comp (fun k => T.matrix k i j * star (T.matrix k l m))]
  rw [this]
  split_ifs <;> simp

theorem x8_main [Nonempty A] [Nonempty K] (T : UnitaryBasis A K) :
    ∀ rho : Matrix A A ℂ,
      ((Fintype.card A : ℂ)^2)⁻¹ • (∑ k, T.matrix k * rho * (T.matrix k)ᴴ) =
        (rho.trace / (Fintype.card A : ℂ)) • (1 : Matrix A A ℂ) := by
  intro rho
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext i m
  rw [Matrix.smul_apply, Matrix.smul_apply, one_apply, Matrix.sum_apply]
  have : ∀ k, (T.matrix k * rho * (T.matrix k)ᴴ) i m =
      ∑ j, ∑ l, rho j l * (T.matrix k i j * star (T.matrix k m l)) := by
    intro k
    simp only [mul_apply, conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [this]
  have key : ∑ k, ∑ j, ∑ l, rho j l * (T.matrix k i j * star (T.matrix k m l)) =
      ∑ j, ∑ l, rho j l * (if (i, j) = (m, l) then (Fintype.card A : ℂ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_sum, x8_complete T]
  rw [key]
  by_cases h : i = m
  · subst h
    have : ∀ j, ∑ l, rho j l * (if (i, j) = (i, l) then (Fintype.card A : ℂ) else 0) =
        rho j j * (Fintype.card A : ℂ) := by
      intro j
      rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hl; simp [Ne.symm hl]
      · simp
    simp only [this, if_true, smul_eq_mul, mul_one]
    rw [← Finset.sum_mul, trace]
    simp only [diag]
    field_simp
  · have : ∀ j l, rho j l * (if (i, j) = (m, l) then (Fintype.card A : ℂ) else 0) = 0 := by
      intro j l; simp [h]
    simp [this, h]

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped Matrix in
open QAlgorithms.Papers.Independent.Gap48.P36 in
theorem solution {A K : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
    [Nonempty A] [Nonempty K] (T : UnitaryBasis A K) :
    ∀ rho : Matrix A A ℂ,
      ((Fintype.card A : ℂ)^2)⁻¹ • (∑ k, T.matrix k * rho * (T.matrix k)ᴴ) =
        (rho.trace / (Fintype.card A : ℂ)) • (1 : Matrix A A ℂ) :=
  x8_main T
