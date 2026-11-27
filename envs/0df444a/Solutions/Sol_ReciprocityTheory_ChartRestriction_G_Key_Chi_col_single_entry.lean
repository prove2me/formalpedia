-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.col_single_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:28:43.369882+00:00
-- url     : https://prove2.me/submissions/0ea4c980-c9d9-49b6-a036-2e7b44df9750

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
theorem _root_.solution {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) {p r0 : Fin g ⊕ Fin g} (h : ∀ r, r ≠ r0 → M r p = 0)
    (q : Fin g ⊕ Fin g) : M r0 p * (J (Fin g) ℤ * M) r0 q = J (Fin g) ℤ p q := by
  exact symplectic_entry_mul_J_mul_of_single_column_entry hM h q
end ReciprocityTheory.ChartRestriction.G.Key.Chi
