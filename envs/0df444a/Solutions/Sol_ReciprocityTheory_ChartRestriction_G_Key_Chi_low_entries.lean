-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.low_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:15:43.901923+00:00
-- url     : https://prove2.me/submissions/654b7a88-27e1-4a63-8722-cc7de7eb5e06

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
private theorem J_mul_apply_inl (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (j : Fin g)
    (q : Fin g ⊕ Fin g) : (J (Fin g) ℤ * M) (Sum.inl j) q = -M (Sum.inr j) q := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
private theorem symplectic_entry_mul_J_mul_of_single_column_entry {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) {p r0 : Fin g ⊕ Fin g} (h : ∀ r, r ≠ r0 → M r p = 0)
    (q : Fin g ⊕ Fin g) : M r0 p * (J (Fin g) ℤ * M) r0 q = J (Fin g) ℤ p q := by
  have h1 := SymplecticGroup.mem_iff.1 (SymplecticGroup.transpose_mem hM)
  rw [Matrix.transpose_transpose, Matrix.mul_assoc] at h1
  have h2 := congrArg (fun A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ => A p q) h1
  rw [Matrix.mul_apply, Finset.sum_eq_single r0] at h2
  · rw [Matrix.transpose_apply] at h2
    exact h2
  · intro r _ hr
    rw [Matrix.transpose_apply, h r hr, zero_mul]
  · intro hr
    exact absurd (Finset.mem_univ _) hr
end ReciprocityTheory.ChartRestriction.G.Key.Chi
end

set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {k : ℕ} {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k M) {i j : Fin g} (hi : (i : ℕ) < k)
    (hj : k ≤ (j : ℕ)) : M (Sum.inl i) (Sum.inl j) = 0 ∧ M (Sum.inr i) (Sum.inl j) = 0 := by
  have hi1 := hF i hi
  have hA : ∀ r, r ≠ Sum.inl i → M r (Sum.inl i) = 0 := fun r hr => by
    rw [hi1.1 r, Matrix.one_apply_ne hr]
  have hB : ∀ r, r ≠ Sum.inr i → M r (Sum.inr i) = 0 := fun r hr => by
    rw [hi1.2 r, Matrix.one_apply_ne hr]
  have hA1 : M (Sum.inl i) (Sum.inl i) = 1 := by rw [hi1.1, Matrix.one_apply_eq]
  have hB1 : M (Sum.inr i) (Sum.inr i) = 1 := by rw [hi1.2, Matrix.one_apply_eq]
  have hij : i ≠ j := fun h => by subst h; omega
  have e1 := symplectic_entry_mul_J_mul_of_single_column_entry hM hA (Sum.inl j)
  have e2 := symplectic_entry_mul_J_mul_of_single_column_entry hM hB (Sum.inl j)
  rw [hA1, one_mul, J_mul_apply_inl] at e1
  rw [hB1, one_mul] at e2
  constructor
  · simpa [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hij] using e2
  · simpa [Matrix.J] using e1
end ReciprocityTheory.ChartRestriction.G.Key.Chi
