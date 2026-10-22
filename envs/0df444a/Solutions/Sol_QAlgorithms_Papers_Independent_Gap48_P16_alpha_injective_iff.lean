-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.alpha_injective_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:00:28.47971+00:00
-- url     : https://prove2.me/submissions/5f28ae4d-ec12-47f9-ab36-99016b914ec8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16
noncomputable section

universe u

open QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Pairings

variable {R A P Q B M : Type u} [CommRing R]

variable [AddCommGroup A] [Module R A] [AddCommGroup P] [Module R P]

variable [AddCommGroup Q] [Module R Q] [AddCommGroup B] [Module R B]

variable [AddCommGroup M] [Module R M]

theorem g74b_exists_fin {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (x : M ⊗[R] N) :
    ∃ (n : ℕ) (m : Fin n → M) (p : Fin n → N), x = ∑ i, m i ⊗ₜ[R] p i := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a b => exact ⟨1, fun _ => a, fun _ => b, by simp⟩
  | add x y hx hy =>
    obtain ⟨n, m, p, rfl⟩ := hx
    obtain ⟨n', m', p', rfl⟩ := hy
    refine ⟨n + n', Fin.append m m', Fin.append p p', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

theorem g74b_alpha_sum {R A P M : Type u} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
    (b : P →ₗ[R] A →ₗ[R] R) {n : ℕ} (m : Fin n → M) (p : Fin n → P) (a : A) :
    pairingAlpha b M (∑ i, m i ⊗ₜ[R] p i) a = ∑ i, b (p i) a • m i := by
  rw [map_sum, LinearMap.sum_apply]
  rfl

/-- Proposition 2.1, PDF pp.3-4: the finite-presentation kernel criterion. -/
theorem solution (b : P →ₗ[R] A →ₗ[R] R) :
    Function.Injective (pairingAlpha b M) ↔
      ∀ (n : ℕ) (m : Fin n → M) (p : Fin n → P),
        ((∑ i, m i ⊗ₜ[R] p i) = 0 ↔ ∀ a : A, (∑ i, b (p i) a • m i) = 0) := by
  constructor
  · intro hinj n m p
    rw [← map_eq_zero_iff _ hinj, LinearMap.ext_iff]
    simp only [g74b_alpha_sum, LinearMap.zero_apply]
  · intro H
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨n, m, p, rfl⟩ := g74b_exists_fin x
    rw [H n m p]
    intro a
    rw [← g74b_alpha_sum, hx, LinearMap.zero_apply]


end Pairings



end
