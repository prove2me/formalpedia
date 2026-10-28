-- Prove2me | solution 1 for SpikedWishart.SoftEdge.eq_65
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T09:23:37.030218+00:00
-- url     : https://prove2.me/submissions/6b016325-3528-494d-9117-a837e78b81cf

import Mathlib

namespace Prove2SwarmSubmission

open MeasureTheory
open scoped BigOperators Matrix

namespace SpikedWishart.SoftEdge

/-! ## Combinatorial determinant helpers

The integration argument below first expands both determinants.  The resulting
double sum over permutations is independent of the measure, so it is convenient
to isolate the exact finite-sum identity here. -/

private lemma sign_sq_real {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ)) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- Expand the product of two determinants as a double sum over permutations. -/
private lemma det_mul_det_expand {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) :
    A.det * B.det =
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)) *
          ∏ k, A (σ k) k * B (τ k) k := by
  rw [Matrix.det_apply', Matrix.det_apply']
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  rw [Finset.prod_mul_distrib]
  ring

/-- Reindexing a product along the inverse of a permutation. -/
private lemma prod_inv_apply {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (σ τ : Equiv.Perm (Fin N)) :
    ∏ k, G (σ k) (τ⁻¹ k) = ∏ i, G (σ (τ i)) i := by
  symm
  simpa using (Equiv.prod_comp τ (fun i : Fin N => G (σ i) (τ⁻¹ i)))

/-- For fixed `σ`, the sum over `τ` is the determinant of the row-permuted
matrix `G.submatrix σ id`. -/
private lemma sum_perm_inner {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (σ : Equiv.Perm (Fin N)) :
    (∑ τ : Equiv.Perm (Fin N),
      (((Equiv.Perm.sign τ : ℤ) : ℝ)) * ∏ k, G (σ k) (τ k))
      = (G.submatrix (⇑σ) id).det := by
  rw [Matrix.det_apply']
  calc
    (∑ τ : Equiv.Perm (Fin N),
        (((Equiv.Perm.sign τ : ℤ) : ℝ)) * ∏ k, G (σ k) (τ k))
        = ∑ τ : Equiv.Perm (Fin N),
            (((Equiv.Perm.sign τ⁻¹ : ℤ) : ℝ)) *
              ∏ k, G (σ k) (τ⁻¹ k) := by
          rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin N)))
            (fun τ : Equiv.Perm (Fin N) =>
              (((Equiv.Perm.sign τ : ℤ) : ℝ)) * ∏ k, G (σ k) (τ k))]
          apply Finset.sum_congr rfl
          intro τ _
          simp [Equiv.inv_apply]
    _ = ∑ τ : Equiv.Perm (Fin N),
          (((Equiv.Perm.sign τ : ℤ) : ℝ)) * ∏ i, G (σ (τ i)) i := by
          apply Finset.sum_congr rfl
          intro τ _
          rw [Equiv.Perm.sign_inv]
          congr 1
          exact prod_inv_apply G σ τ
    _ = ∑ τ : Equiv.Perm (Fin N),
          (((Equiv.Perm.sign τ : ℤ) : ℝ)) *
            ∏ i, (G.submatrix (⇑σ) id) (τ i) i := by
          apply Finset.sum_congr rfl
          intro τ _
          simp [Matrix.submatrix]

/-- The complete permutation/sign/N! identity. -/
private lemma sum_perm_perm {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) :
    (∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)) *
        ∏ k, G (σ k) (τ k))
      = (N.factorial : ℝ) * G.det := by
  calc
    (∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)) *
          ∏ k, G (σ k) (τ k))
        = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤ) : ℝ) *
            (∑ τ : Equiv.Perm (Fin N),
              (((Equiv.Perm.sign τ : ℤ) : ℝ)) * ∏ k, G (σ k) (τ k))) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro τ _
          ring
    _ = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ((G.submatrix (⇑σ) id).det)) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [sum_perm_inner]
    _ = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤ) : ℝ) *
          (((Equiv.Perm.sign σ : ℤ) : ℝ) * G.det)) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Matrix.det_permute]
    _ = ∑ _σ : Equiv.Perm (Fin N), G.det := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [← mul_assoc, sign_sq_real, one_mul]
    _ = (N.factorial : ℝ) * G.det := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, nsmul_eq_mul]

/-! ## Andreief's identity -/

theorem eq_65 {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (N : ℕ)
    (f g : Fin N → α → ℝ) (hfg : ∀ j k, Integrable (fun x => f j x * g k x) μ) :
    ∫ x : Fin N → α, (Matrix.of fun j k => f j (x k)).det * (Matrix.of fun j k => g j (x k)).det
        ∂(Measure.pi fun _ => μ) =
      (N.factorial : ℝ) * (Matrix.of fun j k => ∫ y, f j y * g k y ∂μ).det := by
  classical
  let P : Measure (Fin N → α) := Measure.pi fun _ => μ
  let G : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.of fun j k => ∫ y, f j y * g k y ∂μ
  let term : Equiv.Perm (Fin N) → Equiv.Perm (Fin N) → (Fin N → α) → ℝ :=
    fun σ τ x =>
      (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)) *
        ∏ k, f (σ k) (x k) * g (τ k) (x k)
  have hpointwise : ∀ x : Fin N → α,
      (Matrix.of fun j k => f j (x k)).det * (Matrix.of fun j k => g j (x k)).det
        = ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N), term σ τ x := by
    intro x
    simpa [term] using
      (det_mul_det_expand
        (Matrix.of fun j k => f j (x k))
        (Matrix.of fun j k => g j (x k)))
  have hterm : ∀ σ τ : Equiv.Perm (Fin N), Integrable (term σ τ) P := by
    intro σ τ
    have hprod : Integrable
        (fun x : Fin N → α => ∏ k, f (σ k) (x k) * g (τ k) (x k)) P := by
      simpa [P] using
        (Integrable.fintype_prod
          (μ := fun _ : Fin N => μ)
          (f := fun k y => f (σ k) y * g (τ k) y)
          (fun k => hfg (σ k) (τ k)))
    simpa [term] using hprod.const_mul
      (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ))
  have hsumτ : ∀ σ : Equiv.Perm (Fin N),
      Integrable (fun x : Fin N → α => ∑ τ : Equiv.Perm (Fin N), term σ τ x) P := by
    intro σ
    exact integrable_finsetSum Finset.univ (fun τ _ => hterm σ τ)
  calc
    ∫ x : Fin N → α, (Matrix.of fun j k => f j (x k)).det *
        (Matrix.of fun j k => g j (x k)).det ∂(Measure.pi fun _ => μ)
        = ∫ x : Fin N → α,
            ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N), term σ τ x ∂P := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpointwise x
    _ = ∑ σ : Equiv.Perm (Fin N),
          ∫ x : Fin N → α, ∑ τ : Equiv.Perm (Fin N), term σ τ x ∂P := by
          rw [integral_finsetSum]
          intro σ _
          exact hsumτ σ
    _ = ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
          ∫ x : Fin N → α, term σ τ x ∂P := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [integral_finsetSum]
          intro τ _
          exact hterm σ τ
    _ = ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
          (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)) *
            ∏ k, ∫ y, f (σ k) y * g (τ k) y ∂μ := by
          apply Finset.sum_congr rfl
          intro σ _
          apply Finset.sum_congr rfl
          intro τ _
          rw [integral_const_mul]
          congr 1
          simpa [P] using
            (integral_fintype_prod_eq_prod
              (μ := fun _ : Fin N => μ)
              (f := fun k y => f (σ k) y * g (τ k) y))
    _ = ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
          (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)) *
            ∏ k, G (σ k) (τ k) := by
          simp [G]
    _ = (N.factorial : ℝ) * G.det := sum_perm_perm G
    _ = (N.factorial : ℝ) *
          (Matrix.of fun j k => ∫ y, f j y * g k y ∂μ).det := by
          simp [G]

end SpikedWishart.SoftEdge

end Prove2SwarmSubmission

open MeasureTheory
theorem solution {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (N : ℕ)
    (f g : Fin N → α → ℝ) (hfg : ∀ j k, Integrable (fun x => f j x * g k x) μ) :
    ∫ x : Fin N → α, (Matrix.of fun j k => f j (x k)).det * (Matrix.of fun j k => g j (x k)).det
        ∂(Measure.pi fun _ => μ) =
      (N.factorial : ℝ) * (Matrix.of fun j k => ∫ y, f j y * g k y ∂μ).det := by
  exact Prove2SwarmSubmission.SpikedWishart.SoftEdge.eq_65 μ N f g hfg
