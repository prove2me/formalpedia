-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.phase2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:09.793818+00:00
-- url     : https://prove2.me/submissions/40d32901-ada2-40bd-ba95-edc3cf8081b6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenFin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_mem
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
theorem _root_.solution (k : Fin g) (n : ℕ) : ∀ M ∈ symplecticGroup (Fin g) ℤ, ColsFixed k M →
    (∀ j, M (Sum.inr j) (Sum.inl k) = 0) → ∑ j, (M (Sum.inl j) (Sum.inl k)).natAbs = n →
    ∃ O ∈ spH g, ColsFixed k O ∧ (∀ j, (O * M) (Sum.inr j) (Sum.inl k) = 0) ∧
      ∀ i j, (O * M) (Sum.inl i) (Sum.inl k) ≠ 0 → (O * M) (Sum.inl j) (Sum.inl k) ≠ 0 → i = j := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hM hF hbot hsum
  by_cases hone : ∀ i j, M (Sum.inl i) (Sum.inl k) ≠ 0 → M (Sum.inl j) (Sum.inl k) ≠ 0 → i = j
  · exact ⟨1, (spH g).one_mem, colsFixed_one _, by simpa using hbot, by simpa using hone⟩
  push_neg at hone
  obtain ⟨a, b, ha, hb, hab⟩ := hone
  wlog hle : (M (Sum.inl b) (Sum.inl k)).natAbs ≤ (M (Sum.inl a) (Sum.inl k)).natAbs generalizing a b
  · exact this b a hb ha (Ne.symm hab) (by omega)
  have hak : (k : ℕ) ≤ a := by
    by_contra hlt
    push_neg at hlt
    exact ha (symplectic_inl_inl_eq_zero_of_colsFixed hM hF hlt (fun h => by subst h; exact lt_irrefl _ hlt))
  have hbk : (k : ℕ) ≤ b := by
    by_contra hlt
    push_neg at hlt
    exact hb (symplectic_inl_inl_eq_zero_of_colsFixed hM hF hlt (fun h => by subst h; exact lt_irrefl _ hlt))
  let t : ℤ := M (Sum.inl a) (Sum.inl k) / M (Sum.inl b) (Sum.inl k)
  let E : Matrix (Fin g) (Fin g) ℤ :=
    Matrix.of fun c u => (if c = u then (1 : ℤ) else 0) - if c = a ∧ u = b then t else 0
  let E' : Matrix (Fin g) (Fin g) ℤ :=
    Matrix.of fun c u => (if c = u then (1 : ℤ) else 0) + if c = a ∧ u = b then t else 0
  have hEE' : E * E' = 1 := by
    ext c d
    simp [E, E', Matrix.mul_apply, Matrix.one_apply, sub_mul, mul_add, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ite_and]
    split_ifs <;> simp_all
  have hE'E : E' * E = 1 := by
    ext c d
    simp [E, E', Matrix.mul_apply, Matrix.one_apply, add_mul, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ite_and]
    split_ifs <;> simp_all
  let U : (Matrix (Fin g) (Fin g) ℤ)ˣ := ⟨E, E', hEE', hE'E⟩
  have hO1 : spDiag U ∈ spH g := spDiag_mem U
  have hF1 : ColsFixed k (spDiag U) := by
    intro i hi
    have hia : i ≠ a := fun h => by subst h; omega
    have hib : i ≠ b := fun h => by subst h; omega
    have e1 : ∀ c : Fin g, (i = c ↔ c = i) := fun c => eq_comm
    constructor <;> intro r <;> rcases r with c | c <;>
      simp [spDiag, U, E, E', Matrix.fromBlocks, Matrix.one_apply, hia, hib, e1]
  have hnew : ∀ c, (spDiag U * M) (Sum.inl c) (Sum.inl k) =
      M (Sum.inl c) (Sum.inl k) - if c = a then t * M (Sum.inl b) (Sum.inl k) else 0 := by
    intro c
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp [spDiag, U, E, Matrix.fromBlocks, hbot, sub_mul, Finset.sum_sub_distrib, ite_and]
  have hbot1 : ∀ j, (spDiag U * M) (Sum.inr j) (Sum.inl k) = 0 := by
    intro j
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp [spDiag, Matrix.fromBlocks, hbot]
  have hkey : (M (Sum.inl a) (Sum.inl k) - t * M (Sum.inl b) (Sum.inl k)).natAbs <
      (M (Sum.inl a) (Sum.inl k)).natAbs := by
    have he : M (Sum.inl a) (Sum.inl k) - t * M (Sum.inl b) (Sum.inl k) =
        M (Sum.inl a) (Sum.inl k) % M (Sum.inl b) (Sum.inl k) := by
      rw [Int.emod_def]
      ring
    have h1 := Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg (M (Sum.inl a) (Sum.inl k)) hb)
      (Int.emod_lt (M (Sum.inl a) (Sum.inl k)) hb)
    have h2 : (M (Sum.inl a) (Sum.inl k) % M (Sum.inl b) (Sum.inl k)).natAbs <
        (M (Sum.inl b) (Sum.inl k)).natAbs := by
      simp only [Int.natCast_natAbs] at h1
      rwa [Int.natAbs_abs] at h1
    rw [he]
    omega
  have hlt : ∑ j, ((spDiag U * M) (Sum.inl j) (Sum.inl k)).natAbs < n := by
    rw [← hsum]
    apply Finset.sum_lt_sum
    · intro j _
      rw [hnew]
      by_cases hja : j = a
      · subst hja
        simp only [if_true]
        exact hkey.le
      · simp [hja]
    · exact ⟨a, Finset.mem_univ _, by rw [hnew]; simpa using hkey⟩
  have hM1 : spDiag U * M ∈ symplecticGroup (Fin g) ℤ :=
    (symplecticGroup (Fin g) ℤ).mul_mem (spH_le g hO1) hM
  obtain ⟨O2, hO2, hF2, hb2, hone2⟩ := ih _ hlt (spDiag U * M) hM1 (colsFixed_mul hF1 hF) hbot1 rfl
  refine ⟨O2 * spDiag U, (spH g).mul_mem hO2 hO1, colsFixed_mul hF2 hF1, ?_, ?_⟩
  · simpa [Matrix.mul_assoc] using hb2
  · simpa [Matrix.mul_assoc] using hone2
end ReciprocityTheory.ChartRestriction.G.Key.Chi
