-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_10
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:20:22.615572+00:00
-- url     : https://prove2.me/submissions/7adbdbff-eb8f-48a4-a49f-9e19453c1bf5

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
noncomputable section
open Filter MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)
open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
open scoped MatrixOrder

def g68m_pe {D : Type*} {n : ℕ} (p : Equiv.Perm (Fin n)) : (Fin n → D) ≃ (Fin n → D) where
  toFun x := x ∘ p
  invFun x := x ∘ p.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

lemma g68m_sqrt_inv {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}
    (rho : Op (Fin n → D)) (hrho : rho.PosSemidef) (hinv : copyPermutationInvariant rho)
    (p : Equiv.Perm (Fin n)) (x y : Fin n → D) :
    CFC.sqrt rho (x ∘ p) (y ∘ p) = CFC.sqrt rho x y := by
  set S := CFC.sqrt rho
  have hρ : (0 : Op (Fin n → D)) ≤ rho := Matrix.nonneg_iff_posSemidef.mpr hrho
  have hS0 : (0 : Op (Fin n → D)) ≤ S := CFC.sqrt_nonneg rho
  have hSS : S * S = rho := CFC.sqrt_mul_sqrt_self rho hρ
  set S' := S.submatrix (g68m_pe p) (g68m_pe p)
  have hS'0 : (0 : Op (Fin n → D)) ≤ S' := by
    rw [Matrix.nonneg_iff_posSemidef] at hS0 ⊢
    exact hS0.submatrix _
  have hS'S' : S' * S' = rho := by
    rw [Matrix.submatrix_mul_equiv, hSS]
    exact hinv p
  have := CFC.sqrt_unique hS'S' hS'0
  have h2 := congrFun (congrFun this x) y
  exact h2.symm


attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {D R : Type*} [Fintype D] [Fintype R]
    [DecidableEq D] [DecidableEq R] [Nonempty D] [Nonempty R]
    (n : ℕ) (rho : Op (Fin n → D)) (hrho : rho.PosSemidef)
    (hinv : copyPermutationInvariant rho) (hdim : Fintype.card D ≤ Fintype.card R) :
    ∃ psi : ((Fin n → D) × (Fin n → R)) → ℂ,
      UnnormalizedPurifies psi rho ∧ ∀ (p : Equiv.Perm (Fin n)) x,
        psi (x.1 ∘ p, x.2 ∘ p) = psi x := by
  classical
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hdim
  set S := CFC.sqrt rho
  let ιn : (Fin n → D) → (Fin n → R) := fun z => ι ∘ z
  have hιn : Function.Injective ιn := by
    intro z z' h; funext i; exact ι.injective (congrFun h i)
  let psi : ((Fin n → D) × (Fin n → R)) → ℂ := fun q =>
    if h : ∃ z, ιn z = q.2 then S q.1 h.choose else 0
  have hpsi1 : ∀ x z, psi (x, ιn z) = S x z := by
    intro x z
    have h : ∃ w, ιn w = ιn z := ⟨z, rfl⟩
    simp only [psi, dif_pos h]
    rw [hιn h.choose_spec]
  have hpsi0 : ∀ x y, (¬ ∃ z, ιn z = y) → psi (x, y) = 0 := by
    intro x y h; simp only [psi, dif_neg h]
  refine ⟨psi, ?_, ?_⟩
  · unfold UnnormalizedPurifies
    ext x x'
    simp only [traceRight, vectorOuterProduct, pureDensity, Matrix.of_apply, PiLp.toLp_apply]
    rw [← Fintype.sum_of_injective ιn hιn (fun z => S x z * (starRingEnd ℂ) (S x' z))
      (fun y => psi (x, y) * (starRingEnd ℂ) (psi (x', y)))]
    · have hS0 : (0 : Op (Fin n → D)) ≤ S := CFC.sqrt_nonneg rho
      have hSH : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian
      have hρ : (0 : Op (Fin n → D)) ≤ rho := Matrix.nonneg_iff_posSemidef.mpr hrho
      have hSS : S * S = rho := CFC.sqrt_mul_sqrt_self rho hρ
      rw [← hSS, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro z _
      congr 1
      have := congrFun (congrFun hSH z) x'
      rw [← this]; simp [Matrix.conjTranspose_apply]
    · intro y hy
      rw [hpsi0 x y (fun ⟨z, hz⟩ => hy ⟨z, hz⟩)]; simp
    · intro z; simp only [hpsi1]
  · rintro p ⟨x, y⟩
    simp only
    by_cases hy : ∃ z, ιn z = y
    · obtain ⟨z, rfl⟩ := hy
      have : ιn z ∘ p = ιn (z ∘ p) := rfl
      rw [this, hpsi1, hpsi1]
      exact g68m_sqrt_inv rho hrho hinv p x z
    · have hy' : ¬ ∃ z, ιn z = y ∘ p := by
        rintro ⟨w, hw⟩
        apply hy
        refine ⟨w ∘ p.symm, ?_⟩
        funext i
        have := congrFun hw (p.symm i)
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
        exact this
      rw [hpsi0 _ _ hy', hpsi0 _ _ hy]

end
