-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.col_inl_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:24.119983+00:00
-- url     : https://prove2.me/submissions/55d11db3-5a31-49f8-86fc-c6925dd3230f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenFin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_phase2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_move_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sign_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_phase1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spH_le

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
private theorem symplectic_sum_pair_eq_J {A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hA : A ∈ symplecticGroup (Fin g) ℤ) (p q : Fin g ⊕ Fin g) :
    ∑ b, (A (Sum.inr b) p * A (Sum.inl b) q - A (Sum.inl b) p * A (Sum.inr b) q) =
      J (Fin g) ℤ p q := by
  have h := SymplecticGroup.transpose_mem hA
  rw [SymplecticGroup.mem_iff, Matrix.transpose_transpose] at h
  rw [← h]
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.transpose_apply]
  simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, Finset.sum_sub_distrib, sub_eq_add_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
private theorem symplectic_inl_inl_eq_zero_of_colsFixed {k : ℕ} {A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hA : A ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k A) {i m : Fin g} (hi : (i : ℕ) < k)
    (hm : m ≠ i) : A (Sum.inl i) (Sum.inl m) = 0 := by
  have h := symplectic_sum_pair_eq_J hA (Sum.inr i) (Sum.inl m)
  obtain ⟨-, h2⟩ := hF i hi
  simpa [h2, Matrix.one_apply, Matrix.J, Matrix.fromBlocks, Ne.symm hm] using h
end ReciprocityTheory.ChartRestriction.G.Key.Chi
end

set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution (k : Fin g) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k M) :
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ r,
      (O * M) r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by
  classical
  obtain ⟨O1, hO1, hF1, hb1⟩ := phase1 k _ M hM hF rfl
  have hM1 : O1 * M ∈ symplecticGroup (Fin g) ℤ :=
    (symplecticGroup (Fin g) ℤ).mul_mem (spH_le g hO1) hM
  obtain ⟨O2, hO2, hF2, hb2, hone2⟩ := phase2 k _ (O1 * M) hM1 (colsFixed_mul hF1 hF) hb1 rfl
  have hA : O2 * (O1 * M) ∈ symplecticGroup (Fin g) ℤ :=
    (symplecticGroup (Fin g) ℤ).mul_mem (spH_le g hO2) hM1
  have hFA : ColsFixed k (O2 * (O1 * M)) := colsFixed_mul hF2 (colsFixed_mul hF1 hF)
  have hid := symplectic_sum_pair_eq_J hA (Sum.inl k) (Sum.inr k)
  simp only [hb2, zero_mul, zero_sub] at hid
  simp [Matrix.J, Matrix.fromBlocks, Finset.sum_neg_distrib] at hid
  obtain ⟨j, hj⟩ : ∃ j, (O2 * (O1 * M)) (Sum.inl j) (Sum.inl k) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    simp [hcon] at hid
  have hz : ∀ c, c ≠ j → (O2 * (O1 * M)) (Sum.inl c) (Sum.inl k) = 0 := by
    intro c hc
    by_contra h
    exact hc (hone2 c j h hj)
  have hsupp : ∀ r, (O2 * (O1 * M)) r (Sum.inl k) =
      if r = Sum.inl j then (O2 * (O1 * M)) (Sum.inl j) (Sum.inl k) else 0 := by
    intro r
    rcases r with c | c
    · by_cases hc : c = j
      · subst hc
        simp
      · simp [hc, hz c hc]
    · simp [hb2]
  rw [Finset.sum_eq_single j (fun c _ hc => by rw [hz c hc, zero_mul]) (by simp)] at hid
  have hs := Int.eq_one_or_neg_one_of_mul_eq_one hid
  have hjk : (k : ℕ) ≤ j := by
    by_contra hlt
    push_neg at hlt
    exact hj (symplectic_inl_inl_eq_zero_of_colsFixed hA hFA hlt (fun h => by subst h; exact lt_irrefl _ hlt))
  rcases eq_or_ne j k with hjk' | hjk'
  · rw [hjk'] at hsupp hs
    obtain ⟨O3, hO3, hF3, h3⟩ := sign_col k _ hs _ hsupp
    refine ⟨O3 * O2 * O1, (spH g).mul_mem ((spH g).mul_mem hO3 hO2) hO1,
      colsFixed_mul (colsFixed_mul hF3 hF2) hF1, fun r => ?_⟩
    simpa [Matrix.mul_assoc] using h3 r
  · obtain ⟨O3, hO3, hF3, h3⟩ := move_col k j hjk hjk' _ _ hsupp
    obtain ⟨O4, hO4, hF4, h4⟩ := sign_col k _ hs _ h3
    refine ⟨O4 * O3 * O2 * O1, (spH g).mul_mem ((spH g).mul_mem ((spH g).mul_mem hO4 hO3) hO2) hO1,
      colsFixed_mul (colsFixed_mul (colsFixed_mul hF4 hF3) hF2) hF1, fun r => ?_⟩
    simpa [Matrix.mul_assoc] using h4 r
end ReciprocityTheory.ChartRestriction.G.Key.Chi
