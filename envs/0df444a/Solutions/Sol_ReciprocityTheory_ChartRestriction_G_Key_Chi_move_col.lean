-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.move_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:15:56.512656+00:00
-- url     : https://prove2.me/submissions/fdded819-60f9-4368-a927-445d4fd97a05

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenFin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution (k j : Fin g) (hjk : (k : ℕ) ≤ j) (hne : j ≠ k) (s : ℤ)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hsupp : ∀ r, M r (Sum.inl k) = if r = Sum.inl j then s else 0) :
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ r, (O * M) r (Sum.inl k) = if r = Sum.inl k then s else 0 := by
  classical
  let P : Matrix (Fin g) (Fin g) ℤ := Matrix.of fun a b => if Equiv.swap j k a = b then 1 else 0
  have hP : P * P = 1 := by
    ext a b
    simp only [P, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (Equiv.swap j k a)]
    · simp [Equiv.swap_apply_self, eq_comm]
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  let U : (Matrix (Fin g) (Fin g) ℤ)ˣ := ⟨P, P, hP, hP⟩
  refine ⟨spDiag U, spDiag_mem U, fun i hi => ?_, fun r => ?_⟩
  · have hik : i ≠ k := fun h => by subst h; exact lt_irrefl _ hi
    have hij : i ≠ j := fun h => by subst h; omega
    have hsw : Equiv.swap j k i = i := Equiv.swap_apply_of_ne_of_ne hij hik
    constructor <;> intro r <;> rcases r with a | a
    · have h1 : (Equiv.swap j k a = i) ↔ (a = i) := by rw [Equiv.swap_apply_eq_iff, hsw]
      simp [spDiag, U, P, Matrix.one_apply, Matrix.fromBlocks, h1]
    · simp [spDiag, U, P, Matrix.one_apply, Matrix.fromBlocks]
    · simp [spDiag, U, P, Matrix.one_apply, Matrix.fromBlocks]
    · have h1 : (i = a) ↔ (a = i) := eq_comm
      simp [spDiag, U, P, Matrix.one_apply, Matrix.fromBlocks, Matrix.transpose_apply, hsw, h1]
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with a | a <;>
      simp [spDiag, U, P, hsupp, Matrix.one_apply, Matrix.fromBlocks, Equiv.swap_apply_eq_iff] <;>
      try (split_ifs <;> simp_all)
end ReciprocityTheory.ChartRestriction.G.Key.Chi
