-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.phase1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:49.800457+00:00
-- url     : https://prove2.me/submissions/122850cb-1ff9-42f9-b009-3df7b52e1f37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_low_entries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sum_eJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_mul_inl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_mul_inr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spPJ_mul_inr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_spTransl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_spPJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spGens_subset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spPJ_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_mem


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
theorem _root_.solution (k : Fin g) (n : ℕ) : ∀ M ∈ symplecticGroup (Fin g) ℤ, ColsFixed k M →
    ∑ j, (M (Sum.inr j) (Sum.inl k)).natAbs = n →
    ∃ O ∈ spH g, ColsFixed k O ∧ ∀ j, (O * M) (Sum.inr j) (Sum.inl k) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  intro M hM hF hn
  by_cases hb : ∀ j, M (Sum.inr j) (Sum.inl k) = 0
  · exact ⟨1, Submonoid.one_mem _, colsFixed_one _, fun j => by rw [Matrix.one_mul]; exact hb j⟩
  push_neg at hb
  obtain ⟨j0, hd⟩ := hb
  have hkj0 : (k : ℕ) ≤ (j0 : ℕ) := by
    by_contra hlt
    exact hd (low_entries hM hF (not_le.mp hlt) le_rfl).2
  set a := M (Sum.inl j0) (Sum.inl k) with ha
  set d := M (Sum.inr j0) (Sum.inl k) with hdd
  set S : Matrix (Fin g) (Fin g) ℤ := (-(a / d)) • eJ j0 with hS
  have hSsymm : S.IsSymm := by
    simp [hS, Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_single]
  have hSk : ∀ i : Fin g, (i : ℕ) < k → ∀ l, S l i = 0 := by
    intro i hi l
    have hne : j0 ≠ i := fun h => by subst h; omega
    simp [hS, Matrix.single_apply, hne]
  have hO1 : spPJ j0 * spTransl S ∈ spH g := Submonoid.mul_mem _ (spPJ_mem j0) (spTransl_mem hSsymm)
  have hspH : spH g ≤ symplecticGroup (Fin g) ℤ := Submonoid.closure_le.2 (spGens_subset g)
  have hM' : spPJ j0 * spTransl S * M ∈ symplecticGroup (Fin g) ℤ :=
    Submonoid.mul_mem _ (hspH hO1) hM
  have hF' : ColsFixed k (spPJ j0 * spTransl S * M) :=
    colsFixed_mul (colsFixed_mul (colsFixed_spPJ j0 hkj0) (colsFixed_spTransl hSk)) hF
  have hkey : (a % d).natAbs < d.natAbs := by
    have h1 := Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg a hd) (Int.emod_lt a hd)
    rwa [Int.natAbs_cast] at h1
  have hrow : ∀ j, (spPJ j0 * spTransl S * M) (Sum.inr j) (Sum.inl k) =
      if j = j0 then -(a % d) else M (Sum.inr j) (Sum.inl k) := by
    intro j
    rw [Matrix.mul_assoc, spPJ_mul_inr, spTransl_mul_inl, spTransl_mul_inr]
    split_ifs with hj
    · congr 1
      have e : ∑ l, S j0 l * M (Sum.inr l) (Sum.inl k) = -(a / d) * d := by
        simp only [hS, Matrix.smul_apply, smul_eq_mul, mul_assoc]
        rw [← Finset.mul_sum, sum_eJ, if_pos rfl]
      rw [e, Int.emod_def]
      ring
    · rfl
  have hlt : ∑ j, ((spPJ j0 * spTransl S * M) (Sum.inr j) (Sum.inl k)).natAbs < n := by
    rw [← hn]
    apply Finset.sum_lt_sum
    · intro j _
      rw [hrow j]
      split_ifs with hj
      · subst hj
        rw [Int.natAbs_neg]
        exact hkey.le
      · exact le_rfl
    · refine ⟨j0, Finset.mem_univ _, ?_⟩
      rw [hrow j0, if_pos rfl, Int.natAbs_neg]
      exact hkey
  obtain ⟨O2, hO2, hF2, h2⟩ := ih _ hlt _ hM' hF' rfl
  refine ⟨O2 * (spPJ j0 * spTransl S), Submonoid.mul_mem _ hO2 hO1, colsFixed_mul hF2
    (colsFixed_mul (colsFixed_spPJ j0 hkj0) (colsFixed_spTransl hSk)), fun j => ?_⟩
  rw [Matrix.mul_assoc]
  exact h2 j
end ReciprocityTheory.ChartRestriction.G.Key.Chi
